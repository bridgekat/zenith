//! # Core structures
//!
//! This module defines syntax nodes [`Term`], value objects [`Val`], closure objects [`Clos`] and
//! stack pointers [`Stack`], among other core structures that are allocated on [`Arena`].

use bumpalo::Bump;
use std::cell::Cell;

/// # Terms
///
/// Terms of the core calculus.
///
/// Can be understood as the "source code" given to the evaluator.
#[derive(Debug, Clone, Copy)]
pub enum Term<'a> {
  /// Universe in levels.
  Univ(usize),
  /// Variables in de Bruijn indices.
  Var(usize),
  /// Type annotations (value, type, arena boundary flag).
  Ann(&'a Term<'a>, &'a Term<'a>, bool),
  /// Let expressions (value, *body*).
  Let(&'a Term<'a>, &'a Term<'a>),
  /// Function types (parameter type, *return type*).
  Pi(&'a Term<'a>, &'a Term<'a>),
  /// Function abstractions (*body*).
  Fun(&'a Term<'a>),
  /// Function applications (function, argument).
  App(&'a Term<'a>, &'a Term<'a>),
  /// Tuple types (initial types, *last type*).
  Sig(&'a Term<'a>, &'a Term<'a>),
  /// Tuple constructors (initial values, *last value*).
  Tup(&'a Term<'a>, &'a Term<'a>),
  /// Tuple initial segments (truncation, tuple).
  Init(usize, &'a Term<'a>),
  /// Tuple last element (tuple).
  Last(&'a Term<'a>),
  /// Empty tuple types.
  Unit,
  /// Empty tuple constructors.
  Star,
}

/// # Values
///
/// Values are terms whose outermost `let`s are already collected and frozen at binders.
///
/// Can be understood as "runtime objects" produced by the evaluator.
#[derive(Debug, Clone, Copy)]
pub enum Val<'a, 'b> {
  /// Universe in levels.
  Univ(usize),
  /// Generic variables in de Bruijn *levels* for cheap weakening.
  Gen(usize),
  /// Function types (parameter type, *return type*).
  Pi(&'a Val<'a, 'b>, &'a Clos<'a, 'b>),
  /// Function abstractions (*body*).
  Fun(&'a Clos<'a, 'b>),
  /// Function applications (function, argument).
  App(&'a Val<'a, 'b>, &'a Val<'a, 'b>),
  /// Tuple types (*element types*).
  Sig(&'a [Clos<'a, 'b>]),
  /// Tuple constructors (element values).
  Tup(&'a [Val<'a, 'b>]),
  /// Tuple initial segments (truncation, tuple).
  Init(usize, &'a Val<'a, 'b>),
  /// Tuple last element (tuple).
  Last(&'a Val<'a, 'b>),
}

/// # Closures
///
/// Closures are terms annotated with frozen `let`s capturing the whole environment.
///
/// The environment is represented using a special data structure which supports structural sharing
/// and fast random access (in most cases). For more details, see the documentation for [`Stack`].
#[derive(Debug, Clone, Copy)]
pub struct Clos<'a, 'b> {
  pub env: Stack<'a, 'b>,
  pub body: &'b Term<'b>,
}

/// # Linked list stacks
///
/// The baseline implementation of evaluation environments. Cheap to append and clone, but random
/// access takes linear time. This is acceptable if most of the context is wrapped inside tuples,
/// which have constant-time random access.
#[derive(Debug, Clone, Copy)]
pub enum Stack<'a, 'b> {
  Nil,
  Cons { prev: &'a Stack<'a, 'b>, value: &'a Val<'a, 'b> },
}

/// # Arena allocators
///
/// Mixed-type arena allocators for [`Term`], [`Val`], [`Clos`] and [`Stack`]. These types never
/// allocate memory or manage resources outside the arena, so there is no need to call destructors.
/// It also stores mutable performance counters for debugging and profiling purposes.
#[derive(Debug, Default)]
pub struct Arena {
  data: Bump,
  term_count: Cell<usize>,
  val_count: Cell<usize>,
  clos_count: Cell<usize>,
  frame_count: Cell<usize>,
  lookup_count: Cell<usize>,
  link_count: Cell<usize>,
}

impl Arena {
  /// Creates an empty arena.
  pub fn new() -> Self {
    Self::default()
  }

  /// Allocates a new term.
  pub fn term<'a>(&'a self, term: Term<'a>) -> &'a Term<'a> {
    self.term_count.update(|x| x + 1);
    self.data.alloc(term)
  }

  /// Allocates a new value.
  pub fn val<'a, 'b>(&'a self, val: Val<'a, 'b>) -> &'a Val<'a, 'b> {
    self.val_count.update(|x| x + 1);
    self.data.alloc(val)
  }

  /// Allocates a new array of values for writing.
  pub fn values<'a, 'b>(&'a self, len: usize, nil: Val<'a, 'b>) -> &'a mut [Val<'a, 'b>] {
    self.val_count.update(|x| x + len);
    self.data.alloc_slice_fill_copy(len, nil)
  }

  /// Allocates a new closure.
  pub fn clos<'a, 'b>(&'a self, clos: Clos<'a, 'b>) -> &'a Clos<'a, 'b> {
    self.clos_count.update(|x| x + 1);
    self.data.alloc(clos)
  }

  /// Allocates a new array of closures.
  pub fn closures<'a, 'b>(&'a self, closures: &[Clos<'a, 'b>]) -> &'a [Clos<'a, 'b>] {
    self.clos_count.update(|x| x + closures.len());
    self.data.alloc_slice_copy(closures)
  }

  /// Allocates a new stack item.
  pub fn frame<'a, 'b>(&'a self, stack: Stack<'a, 'b>) -> &'a Stack<'a, 'b> {
    self.frame_count.update(|x| x + 1);
    self.data.alloc(stack)
  }

  /// Increments the stack lookup counter for profiling.
  pub fn inc_lookup_count(&self) {
    self.lookup_count.update(|x| x + 1);
  }

  /// Increments the stack lookup length counter for profiling.
  pub fn inc_link_count(&self) {
    self.link_count.update(|x| x + 1);
  }

  /// Returns the number of terms in the arena.
  pub fn term_count(&self) -> usize {
    self.term_count.get()
  }

  /// Returns the number of values in the arena.
  pub fn val_count(&self) -> usize {
    self.val_count.get()
  }

  /// Returns the number of closures in the arena.
  pub fn clos_count(&self) -> usize {
    self.clos_count.get()
  }

  /// Returns the number of frames in the arena.
  pub fn frame_count(&self) -> usize {
    self.frame_count.get()
  }

  /// Returns the number of stack lookups.
  pub fn lookup_count(&self) -> usize {
    self.lookup_count.get()
  }

  /// Returns the average length of stack lookups.
  pub fn average_link_count(&self) -> f32 {
    self.link_count.get() as f32 / self.lookup_count.get().max(1) as f32
  }

  /// Deallocates all objects and resets all performance counters.
  pub fn reset(&mut self) {
    self.data.reset();
    self.term_count.set(0);
    self.val_count.set(0);
    self.clos_count.set(0);
    self.frame_count.set(0);
    self.lookup_count.set(0);
    self.link_count.set(0);
  }
}
