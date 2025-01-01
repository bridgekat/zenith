use bumpalo::Bump;
use std::cell::Cell;

use crate::elab;
use crate::ir;

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
  char_count: Cell<usize>,
  lookup_count: Cell<usize>,
  link_count: Cell<usize>,
}

impl Arena {
  /// Creates an empty arena.
  pub fn new() -> Self {
    Self::default()
  }

  /// Allocates a new term.
  pub fn term<'a>(&'a self, term: ir::Term<'a>) -> &'a ir::Term<'a> {
    self.term_count.update(|x| x + 1);
    self.data.alloc(term)
  }

  /// Allocates a new named term.
  pub fn named<'a>(&'a self, term: elab::Term<'a>) -> &'a elab::Term<'a> {
    self.term_count.update(|x| x + 1);
    self.data.alloc(term)
  }

  /// Allocates a new value.
  pub fn val<'a, 'b>(&'a self, val: ir::Val<'a, 'b>) -> &'a ir::Val<'a, 'b> {
    self.val_count.update(|x| x + 1);
    self.data.alloc(val)
  }

  /// Allocates a new array of values for writing.
  pub fn values<'a, 'b>(&'a self, len: usize, nil: ir::Val<'a, 'b>) -> &'a mut [ir::Val<'a, 'b>] {
    self.val_count.update(|x| x + len);
    self.data.alloc_slice_fill_copy(len, nil)
  }

  /// Allocates a new closure.
  pub fn clos<'a, 'b>(&'a self, clos: ir::Clos<'a, 'b>) -> &'a ir::Clos<'a, 'b> {
    self.clos_count.update(|x| x + 1);
    self.data.alloc(clos)
  }

  /// Allocates a new array of closures.
  pub fn closures<'a, 'b>(&'a self, closures: &[ir::Clos<'a, 'b>]) -> &'a [ir::Clos<'a, 'b>] {
    self.clos_count.update(|x| x + closures.len());
    self.data.alloc_slice_copy(closures)
  }

  /// Allocates a new stack item.
  pub fn frame<'a, 'b>(&'a self, stack: ir::Stack<'a, 'b>) -> &'a ir::Stack<'a, 'b> {
    self.frame_count.update(|x| x + 1);
    self.data.alloc(stack)
  }

  /// Allocates a new string.
  pub fn string<'a>(&'a self, string: &str) -> &'a str {
    self.char_count.update(|x| x + string.len());
    self.data.alloc_str(string)
  }

  /// Allocates a new array of strings.
  pub fn strings<'a>(&'a self, strings: &[&str]) -> &'a [&'a str] {
    self.data.alloc_slice_copy(&strings.iter().map(|s| self.string(s)).collect::<Vec<_>>())
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
