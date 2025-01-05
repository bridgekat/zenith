use bumpalo::Bump;
use std::cell::Cell;

use super::*;

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
    self.term_count.set(self.term_count.get() + 1);
    self.data.alloc(term)
  }

  /// Allocates a new array of terms for writing.
  pub fn terms(&self, len: usize) -> &mut [Term<'_>] {
    self.term_count.set(self.term_count.get() + len);
    self.data.alloc_slice_fill_copy(len, Term::Univ(0))
  }

  /// Allocates a new value.
  pub fn val<'a>(&'a self, val: Val<'a>) -> &'a Val<'a> {
    self.val_count.set(self.val_count.get() + 1);
    self.data.alloc(val)
  }

  /// Allocates a new array of values for writing.
  pub fn values(&self, len: usize) -> &mut [Val<'_>] {
    self.val_count.set(self.val_count.get() + len);
    self.data.alloc_slice_fill_copy(len, Val::Univ(0))
  }

  /// Allocates a new closure.
  pub fn clos<'a>(&'a self, clos: Clos<'a>) -> &'a Clos<'a> {
    self.clos_count.set(self.clos_count.get() + 1);
    self.data.alloc(clos)
  }

  /// Allocates a new array of closures for writing.
  pub fn closures(&self, len: usize) -> &mut [Clos<'_>] {
    self.clos_count.set(self.clos_count.get() + len);
    self.data.alloc_slice_fill_clone(len, &Clos { env: Stack::Nil, body: &Term::Univ(0) })
  }

  /// Allocates a new stack item.
  pub fn frame<'a>(&'a self, stack: Stack<'a>) -> &'a Stack<'a> {
    self.frame_count.set(self.frame_count.get() + 1);
    self.data.alloc(stack)
  }

  /// Increments the stack lookup counter for profiling.
  pub fn inc_lookup_count(&self) {
    self.lookup_count.set(self.lookup_count.get() + 1);
  }

  /// Increments the stack lookup length counter for profiling.
  pub fn inc_link_count(&self) {
    self.link_count.set(self.link_count.get() + 1);
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

impl Term<'_> {
  /// Clones `self` to given arena.
  pub fn relocate<'a>(&self, ar: &'a Arena) -> Term<'a> {
    match self {
      Term::Gc(x) => Term::Gc(ar.term(x.relocate(ar))),
      Term::Univ(v) => Term::Univ(*v),
      Term::Var(ix) => Term::Var(*ix),
      Term::Ann(x, t) => Term::Ann(ar.term(x.relocate(ar)), ar.term(t.relocate(ar))),
      Term::Let(v, x) => Term::Let(ar.term(v.relocate(ar)), ar.term(x.relocate(ar))),
      Term::Pi(t, u) => Term::Pi(ar.term(t.relocate(ar)), ar.term(u.relocate(ar))),
      Term::Fun(b) => Term::Fun(ar.term(b.relocate(ar))),
      Term::App(f, x) => Term::App(ar.term(f.relocate(ar)), ar.term(x.relocate(ar))),
      Term::Sig(us) => {
        let terms = ar.terms(us.len());
        for (term, u) in terms.iter_mut().zip(us.iter()) {
          *term = u.relocate(ar);
        }
        Term::Sig(terms)
      }
      Term::Tup(bs) => {
        let terms = ar.terms(bs.len());
        for (term, b) in terms.iter_mut().zip(bs.iter()) {
          *term = b.relocate(ar);
        }
        Term::Tup(terms)
      }
      Term::Init(n, x) => Term::Init(*n, ar.term(x.relocate(ar))),
      Term::Proj(n, x) => Term::Proj(*n, ar.term(x.relocate(ar))),
    }
  }
}

impl Val<'_> {
  /// Clones `self` to given arena.
  pub fn relocate<'a>(&self, ar: &'a Arena) -> Val<'a> {
    match self {
      Val::Univ(v) => Val::Univ(*v),
      Val::Free(i) => Val::Free(*i),
      Val::Pi(t, u) => Val::Pi(ar.val(t.relocate(ar)), ar.clos(u.relocate(ar))),
      Val::Fun(b) => Val::Fun(ar.clos(b.relocate(ar))),
      Val::App(f, x) => Val::App(ar.val(f.relocate(ar)), ar.val(x.relocate(ar))),
      Val::Sig(us) => {
        let closures = ar.closures(us.len());
        for (closure, u) in closures.iter_mut().zip(us.iter()) {
          *closure = u.relocate(ar);
        }
        Val::Sig(closures)
      }
      Val::Tup(bs) => {
        let values = ar.values(bs.len());
        for (value, b) in values.iter_mut().zip(bs.iter()) {
          *value = b.relocate(ar);
        }
        Val::Tup(values)
      }
      Val::Init(n, x) => Val::Init(*n, ar.val(x.relocate(ar))),
      Val::Proj(n, x) => Val::Proj(*n, ar.val(x.relocate(ar))),
    }
  }
}

impl Clos<'_> {
  /// Clones `self` to given arena.
  pub fn relocate<'a>(&self, ar: &'a Arena) -> Clos<'a> {
    let Self { env, body } = self;
    Clos { env: env.relocate(ar), body: ar.term(body.relocate(ar)) }
  }
}

impl Stack<'_> {
  /// Clones `self` to given arena.
  pub fn relocate<'a>(&self, ar: &'a Arena) -> Stack<'a> {
    match self {
      Stack::Nil => Stack::Nil,
      Stack::Cons { prev, value } => Stack::Cons { prev: ar.frame(prev.relocate(ar)), value: value.relocate(ar) },
    }
  }
}
