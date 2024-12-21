//! # Core structures
//!
//! This module defines syntax nodes [`Term`], value objects [`Val`] and stack frames [`Frame`],
//! among other core structures that are allocated on [`Arena`].
//!
//! Due to interior mutability in the implemetation of [`Frame`], all structures are invariant over
//! their lifetime generics. This unfortunately makes it impossible to have terms spanning across
//! multiple arenas, which limits the use of arenas as a garbage collection mechanism. This should
//! nevertheless be memory-safe; more code will be migrated to unsafe Rust in the future so as to
//! allow covariance.

use std::cell::UnsafeCell;
use std::mem::ManuallyDrop;
use std::num::NonZeroUsize;

/// # Universes
///
/// A wrapper around universe levels.
///
/// Currently there are only two: 0 for `Type`, 1 for `Kind`.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Univ(pub usize);

/// # Terms
///
/// Terms of the core calculus.
///
/// Can be understood as the "source code" given to the evaluator.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Term<'a> {
  /// Universes.
  Univ(Univ),
  /// Variables in de Bruijn indices.
  Var(usize),
  /// Type annotations (value, type).
  Ann(&'a Term<'a>, &'a Term<'a>),
  /// Let expressions (value, *body*).
  Let(&'a Term<'a>, &'a Term<'a>),
  /// Function types (parameter type, *return type*).
  Pi(&'a Term<'a>, &'a Term<'a>),
  /// Function abstractions (*body*).
  Fun(&'a Term<'a>),
  /// Function applications (function, argument).
  App(&'a Term<'a>, &'a Term<'a>),
  /// Pair types (first type, *second type*).
  Sig(&'a Term<'a>, &'a Term<'a>),
  /// Pair let-constructors (first value, *second value*).
  Pair(&'a Term<'a>, &'a Term<'a>),
  /// Pair projections (pair).
  Fst(&'a Term<'a>),
  /// Pair projections (pair).
  Snd(&'a Term<'a>),
  /// Unit types.
  Unit,
  /// Unit inhabitants.
  Star,
}

/// # Closures
///
/// Closures are terms annotated with frozen `let`s capturing the whole environment.
///
/// The environment is represented using a special data structure which supports structural sharing
/// and fast random access (in most cases). For more details, see the documentation for [`Stack`].
#[derive(Debug, Clone)]
pub struct Clos<'a> {
  pub env: Stack<'a>,
  pub body: &'a Term<'a>,
}

/// # Values
///
/// Values are terms whose outermost `let`s are already collected and frozen at binders.
///
/// Can be understood as "runtime objects" produced by the evaluator.
#[derive(Debug, Clone)]
pub enum Val<'a> {
  /// Universes.
  Univ(Univ),
  /// Generic variables in de Bruijn *levels* for cheap weakening.
  Gen(usize),
  /// Function types (parameter type, *return type*).
  Pi(&'a Val<'a>, Clos<'a>),
  /// Function abstractions (*body*).
  Fun(Clos<'a>),
  /// Function applications (function, argument).
  App(&'a Val<'a>, &'a Val<'a>),
  /// Pair types (first type, *second type*).
  Sig(&'a Val<'a>, Clos<'a>),
  /// Pair let-constructors (first value, *second value*).
  Pair(&'a Val<'a>, Clos<'a>),
  /// Pair projections (pair).
  Fst(&'a Val<'a>),
  /// Pair projections (pair).
  Snd(&'a Val<'a>),
  /// Unit types.
  Unit,
  /// Unit inhabitants.
  Star,
}

/// Entries of [`Frame`]
#[derive(Debug)]
pub struct Entry<'a> {
  pub value: Option<Val<'a>>,
  pub refcount: usize,
}

/// Underlying linked frames of [`Stack`]
#[derive(Debug)]
pub struct Frame<'a> {
  pub prev: Stack<'a>,
  pub entries: UnsafeCell<Vec<Entry<'a>>>,
}

/// # Linked stacks
///
/// In the simplest implementation of NbE, evaluation environments are represented as linked lists
/// of definitions. This becomes infeasible when the environment grows large, as indexing into a
/// linked list is O(n). On the other hand, environments should support fast pushing and cloning
/// (for the creation of closures), and arrays cannot be cloned efficiently. The same tension arises
/// in functional programming language interpreters, and is known as the
/// [upwards funarg problem](https://en.wikipedia.org/wiki/Funarg_problem#Upwards_funarg_problem).
///
/// The situation is worse in theorem provers, where environments are frequently updated. A common
/// solution is to separate the *top-level* context from the *local* context, the former being
/// represented as a hash map or array for fast indexing, while the latter being linked lists.
/// However, dividing the context into two levels is not as flexible and leads to code duplication.
///
/// As a simple but general solution, we use linked lists but store an array of definitions in each
/// node, so that pushing work on arrays whenever possible, and new nodes are created only when
/// strictly necessary (i.e. when branching occurs). Moreover, to reduce the chance of branching,
/// entries at the end of the array are dropped when they are no longer referenced.
#[derive(Debug)]
pub enum Stack<'a> {
  Empty,
  Ptr { frame: &'a Frame<'a>, position: NonZeroUsize },
}

/// # Arena allocators
///
/// A mixed-type arena allocator for [`Term`], [`Val`] and [`Frame`]. This is basically a wrapper
/// around three [`typed_arena::Arena`], but also takes care of the dropping process.
#[derive(Default)]
pub struct Arena<'a> {
  terms: ManuallyDrop<typed_arena::Arena<Term<'a>>>,
  vals: ManuallyDrop<typed_arena::Arena<Val<'a>>>,
  frames: ManuallyDrop<typed_arena::Arena<Frame<'a>>>,
}

impl<'a> Arena<'a> {
  /// Creates an empty arena.
  pub fn new() -> Self {
    Self::default()
  }

  /// Allocates a new term.
  pub fn term(&'a self, term: Term<'a>) -> &'a Term<'a> {
    self.terms.alloc(term)
  }

  /// Allocates a new value.
  pub fn val(&'a self, val: Val<'a>) -> &'a Val<'a> {
    self.vals.alloc(val)
  }

  /// Allocates a new frame.
  pub fn frame(&'a self, frame: Frame<'a>) -> &'a Frame<'a> {
    self.frames.alloc(frame)
  }
}

impl Frame<'_> {
  /// Drops all [`Stack::Ptr`] instances inside `self`.
  ///
  /// To safely drop a [`Frame`], we must drop all [`Stack::Ptr`] referencing it. Rust detects
  /// this problem through [drop check](https://doc.rust-lang.org/nomicon/dropck.html) and rejects
  /// the code unless a custom [`Drop`] implementation is provided, possibly by using the
  /// [unsafe `may_dangle` attribute](https://github.com/rust-lang/rfcs/pull/1327).
  pub fn unlink_ref(&mut self) {
    self.prev = Stack::Empty;
    for entry in self.entries.get_mut().iter_mut() {
      entry.value = None;
    }
  }

  /// Panics if there are still [`Stack::Ptr`] instances referencing `self`.
  ///
  /// To safely drop a [`Frame`], we must drop all [`Stack::Ptr`] referencing it. Rust detects
  /// this problem through [drop check](https://doc.rust-lang.org/nomicon/dropck.html) and rejects
  /// the code unless a custom [`Drop`] implementation is provided, possibly by using the
  /// [unsafe `may_dangle` attribute](https://github.com/rust-lang/rfcs/pull/1327).
  pub fn assert_unref(&mut self) {
    for entry in self.entries.get_mut().iter_mut() {
      if entry.refcount != 0 {
        unreachable!();
      }
    }
  }
}

#[allow(clippy::needless_lifetimes)]
unsafe impl<#[may_dangle] 'a> Drop for Arena<'a> {
  fn drop(&mut self) {
    // SAFETY: terms reference other terms, but their destructors do not read these references.
    unsafe { ManuallyDrop::drop(&mut self.terms) };
    // SAFETY: values reference other values, but their destructors do not read these references.
    unsafe { ManuallyDrop::drop(&mut self.vals) };
    // Unlink all references in frames.
    for frame in self.frames.iter_mut() {
      frame.unlink_ref();
    }
    for frame in self.frames.iter_mut() {
      frame.assert_unref();
    }
    // SAFETY: frames reference other frames, but their destructors do not read these references,
    // as long as all references are already unlinked.
    unsafe { ManuallyDrop::drop(&mut self.frames) };
  }
}
