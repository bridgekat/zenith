//! # Core structures
//!
//! This module defines syntax nodes [`Term`], value objects [`Val`] and stack frames [`Frame`],
//! among other core structures that are allocated on [`Arena`].

use bumpalo::Bump;
use std::cell::UnsafeCell;

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
  /// Pair constructors (first value, second value).
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
  /// Pair constructors (first value, second value).
  Pair(&'a Val<'a>, &'a Val<'a>),
  /// Pair projections (pair).
  Fst(&'a Val<'a>),
  /// Pair projections (pair).
  Snd(&'a Val<'a>),
  /// Unit types.
  Unit,
  /// Unit inhabitants.
  Star,
}

/// # Linked list stacks
///
/// The baseline implementation of evaluation environments.
#[cfg(not(feature = "linked_frame_stacks"))]
#[derive(Debug, Clone)]
pub enum Stack<'a> {
  Nil,
  Cons { prev: &'a Stack<'a>, value: &'a Val<'a> },
}

/// # Linked frame stacks
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
#[cfg(feature = "linked_frame_stacks")]
#[derive(Debug)]
pub enum Stack<'a> {
  Empty,
  Ptr { frame: &'a Frame<'a>, position: std::num::NonZeroUsize },
}

/// # Linked frames of [`Stack`]
///
/// Each frame contains a reference to the previous frame, and an array of entries.
#[cfg(feature = "linked_frame_stacks")]
#[derive(Debug)]
pub struct Frame<'a> {
  pub prev: Stack<'a>,
  pub entries: UnsafeCell<Vec<Entry<'a>, &'a Bump>>,
}

/// # Entries of [`Frame`]
///
/// Each entry contains a value, and a reference count to it as well as all preceding values.
#[cfg(feature = "linked_frame_stacks")]
#[derive(Debug)]
pub struct Entry<'a> {
  pub value: Option<Val<'a>>,
  pub refcount: usize,
}

/// # Arena allocators
///
/// Mixed-type arena allocators for [`Term`], [`Val`] and [`Frame`]. These types never allocate
/// memory or manage resources outside the arena, so there is no need to call destructors.
/// It also stores mutable performance counters for debugging and profiling purposes.
#[derive(Default)]
pub struct Arena {
  data: Bump,
  term_count: UnsafeCell<usize>,
  val_count: UnsafeCell<usize>,
  frame_count: UnsafeCell<usize>,
  lookup_count: UnsafeCell<usize>,
  link_count: UnsafeCell<usize>,
}

impl Arena {
  /// Creates an empty arena.
  pub fn new() -> Self {
    Self::default()
  }

  /// Allocates a new term.
  pub fn term<'a>(&'a self, term: Term<'a>) -> &'a Term<'a> {
    unsafe { (*self.term_count.get()) += 1 };
    self.data.alloc(term)
  }

  /// Allocates a new value.
  pub fn val<'a>(&'a self, val: Val<'a>) -> &'a Val<'a> {
    unsafe { (*self.val_count.get()) += 1 };
    self.data.alloc(val)
  }

  /// Allocates a new stack item.
  #[cfg(not(feature = "linked_frame_stacks"))]
  pub fn frame<'a>(&'a self, stack: Stack<'a>) -> &'a Stack<'a> {
    unsafe { (*self.frame_count.get()) += 1 };
    self.data.alloc(stack)
  }

  /// Allocates a new stack frame with a single entry.
  #[cfg(feature = "linked_frame_stacks")]
  pub fn frame<'a>(&'a self, prev: Stack<'a>, entry: Entry<'a>) -> &'a Frame<'a> {
    unsafe { (*self.frame_count.get()) += 1 };
    let mut entries = Vec::with_capacity_in(1, &self.data);
    entries.push(entry);
    self.data.alloc(Frame { prev, entries: UnsafeCell::new(entries) })
  }

  /// Increments the term counter for profiling.
  pub fn inc_term_count(&self) {
    unsafe { (*self.term_count.get()) += 1 };
  }

  /// Increments the value counter for profiling.
  pub fn inc_val_count(&self) {
    unsafe { (*self.val_count.get()) += 1 };
  }

  /// Increments the frame counter for profiling.
  pub fn inc_frame_count(&self) {
    unsafe { (*self.frame_count.get()) += 1 };
  }

  /// Increments the stack lookup counter for profiling.
  pub fn inc_lookup_count(&self) {
    unsafe { (*self.lookup_count.get()) += 1 };
  }

  /// Increments the stack lookup length counter for profiling.
  pub fn inc_link_count(&self) {
    unsafe { (*self.link_count.get()) += 1 };
  }

  /// Returns the number of terms in the arena.
  pub fn term_count(&self) -> usize {
    unsafe { *self.term_count.get() }
  }

  /// Returns the number of values in the arena.
  pub fn val_count(&self) -> usize {
    unsafe { *self.val_count.get() }
  }

  /// Returns the number of frames in the arena.
  pub fn frame_count(&self) -> usize {
    unsafe { *self.frame_count.get() }
  }

  /// Returns the number of stack lookups.
  pub fn lookup_count(&self) -> usize {
    unsafe { *self.lookup_count.get() }
  }

  /// Returns the average length of stack lookups.
  pub fn average_link_count(&self) -> f32 {
    unsafe { *self.link_count.get() as f32 / (*self.lookup_count.get()).max(1) as f32 }
  }

  /// Deallocates all objects and resets performance counters.
  pub fn reset(&mut self) {
    self.data.reset();
    *self.term_count.get_mut() = 0;
    *self.val_count.get_mut() = 0;
    *self.frame_count.get_mut() = 0;
    *self.lookup_count.get_mut() = 0;
    *self.link_count.get_mut() = 0;
  }
}
