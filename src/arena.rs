use bumpalo::Bump;
use std::cell::Cell;

use crate::ir::{Bound, Clos, Decoration, Field, Stack, Term, Val};

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

/// # Relocation trait
///
/// A trait which serves as the [`Clone`] counterpart for types allocated on an [`Arena`].
/// It is typically implemented for `<'a, T<'a>>` where `T<'a>` is some type containing references
/// with lifetime `'a`. To specify a [`Relocate`] trait bound, use higher-ranked trait bounds
/// `for<'a> Relocate<'a, T<'a>>`.
pub trait Relocate<'a, T> {
  /// Clones `self` to given arena.
  fn relocate(&self, ar: &'a Arena) -> T;
}

impl Arena {
  /// Creates an empty arena.
  pub fn new() -> Self {
    Self::default()
  }

  /// Allocates a new string.
  pub fn string<'b>(&'b self, string: &str) -> &'b str {
    self.data.alloc_str(string)
  }

  /// Allocates a new array of strings.
  pub fn strings<'b>(&'b self, strings: &[&str]) -> &'b [&'b str] {
    self.data.alloc_slice_copy(&strings.iter().map(|s| self.string(s)).collect::<Vec<_>>())
  }

  /// Allocates a new bound variable info.
  pub fn bound<'b>(&'b self, bound: Bound<'b>) -> &'b Bound<'b> {
    self.data.alloc(bound)
  }

  /// Allocates a new field variable info.
  pub fn field<'b>(&'b self, field: Field<'b>) -> &'b Field<'b> {
    self.data.alloc(field)
  }

  /// Allocates a new term.
  pub fn term<'a, 'b, T: Decoration>(&'a self, term: Term<'a, 'b, T>) -> &'a Term<'a, 'b, T> {
    self.term_count.set(self.term_count.get() + 1);
    self.data.alloc(term)
  }

  /// Allocates a new array of terms with field info for writing.
  pub fn terms<'b, T: Decoration>(&self, len: usize) -> &mut [(&'b Field<'b>, Term<'_, 'b, T>)] {
    self.term_count.set(self.term_count.get() + len);
    self.data.alloc_slice_fill_copy(len, (Field::empty(), Term::Univ(0)))
  }

  /// Allocates a new value.
  pub fn val<'a, 'b>(&'a self, val: Val<'a, 'b>) -> &'a Val<'a, 'b> {
    self.val_count.set(self.val_count.get() + 1);
    self.data.alloc(val)
  }

  /// Allocates a new array of values with field info for writing.
  pub fn values<'b>(&self, len: usize) -> &mut [(&'b Field<'b>, Val<'_, 'b>)] {
    self.val_count.set(self.val_count.get() + len);
    self.data.alloc_slice_fill_copy(len, (Field::empty(), Val::Univ(0)))
  }

  /// Allocates a new closure.
  pub fn clos<'a, 'b>(&'a self, clos: Clos<'a, 'b>) -> &'a Clos<'a, 'b> {
    self.clos_count.set(self.clos_count.get() + 1);
    self.data.alloc(clos)
  }

  /// Allocates a new array of closures with field info for writing.
  pub fn closures<'b>(&self, len: usize) -> &mut [(&'b Field<'b>, Clos<'_, 'b>)] {
    let empty = (Field::empty(), Clos { info: Bound::empty(), env: Stack::Nil, body: &Term::Univ(0) });
    self.clos_count.set(self.clos_count.get() + len);
    self.data.alloc_slice_fill_clone(len, &empty)
  }

  /// Allocates a new stack item.
  pub fn frame<'a, 'b>(&'a self, stack: Stack<'a, 'b>) -> &'a Stack<'a, 'b> {
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

impl<'a> Relocate<'a, !> for ! {
  fn relocate(&self, _: &'a Arena) -> ! {
    match *self {}
  }
}

impl<'a> Relocate<'a, &'a str> for &str {
  fn relocate(&self, ar: &'a Arena) -> &'a str {
    ar.string(self)
  }
}

impl<'a, 'b, T: Decoration> Relocate<'a, Term<'a, 'b, T>> for Term<'_, 'b, T> {
  fn relocate(&self, ar: &'a Arena) -> Term<'a, 'b, T> {
    match self {
      Term::Gc(x) => Term::Gc(ar.term(x.relocate(ar))),
      Term::Univ(v) => Term::Univ(*v),
      Term::Var(ix) => Term::Var(*ix),
      Term::Ann(x, t) => Term::Ann(ar.term(x.relocate(ar)), ar.term(t.relocate(ar))),
      Term::Let(info, v, x) => Term::Let(info, ar.term(v.relocate(ar)), ar.term(x.relocate(ar))),
      Term::Pi(info, t, u) => Term::Pi(info, ar.term(t.relocate(ar)), ar.term(u.relocate(ar))),
      Term::Fun(info, b) => Term::Fun(info, ar.term(b.relocate(ar))),
      Term::App(f, x, dot) => Term::App(ar.term(f.relocate(ar)), ar.term(x.relocate(ar)), *dot),
      Term::Sig(us) => {
        let terms = ar.terms(us.len());
        for (term, (info, u)) in terms.iter_mut().zip(us.iter()) {
          *term = (info, u.relocate(ar));
        }
        Term::Sig(terms)
      }
      Term::Tup(bs) => {
        let terms = ar.terms(bs.len());
        for (term, (info, b)) in terms.iter_mut().zip(bs.iter()) {
          *term = (info, b.relocate(ar));
        }
        Term::Tup(terms)
      }
      Term::Init(n, x) => Term::Init(*n, ar.term(x.relocate(ar))),
      Term::Proj(n, x) => Term::Proj(*n, ar.term(x.relocate(ar))),
      Term::Meta(m) => Term::Meta(*m),
      Term::NamedVar(s, ext) => Term::NamedVar(*s, *ext),
      Term::NamedProj(s, x, ext) => Term::NamedProj(*s, ar.term(x.relocate(ar)), *ext),
    }
  }
}

impl<'a, 'b> Relocate<'a, Val<'a, 'b>> for Val<'_, 'b> {
  fn relocate(&self, ar: &'a Arena) -> Val<'a, 'b> {
    match self {
      Val::Univ(v) => Val::Univ(*v),
      Val::Free(i) => Val::Free(*i),
      Val::Pi(t, u) => Val::Pi(ar.val(t.relocate(ar)), ar.clos(u.relocate(ar))),
      Val::Fun(b) => Val::Fun(ar.clos(b.relocate(ar))),
      Val::App(f, x, dot) => Val::App(ar.val(f.relocate(ar)), ar.val(x.relocate(ar)), *dot),
      Val::Sig(us) => {
        let closures = ar.closures(us.len());
        for (closure, (info, u)) in closures.iter_mut().zip(us.iter()) {
          *closure = (info, u.relocate(ar));
        }
        Val::Sig(closures)
      }
      Val::Tup(bs) => {
        let values = ar.values(bs.len());
        for (value, (info, b)) in values.iter_mut().zip(bs.iter()) {
          *value = (info, b.relocate(ar));
        }
        Val::Tup(values)
      }
      Val::Init(n, x) => Val::Init(*n, ar.val(x.relocate(ar))),
      Val::Proj(n, x) => Val::Proj(*n, ar.val(x.relocate(ar))),
      Val::Meta(env, m) => Val::Meta(ar.frame(env.relocate(ar)), *m),
    }
  }
}

impl<'a, 'b> Relocate<'a, Clos<'a, 'b>> for Clos<'_, 'b> {
  fn relocate(&self, ar: &'a Arena) -> Clos<'a, 'b> {
    let Self { info, env, body } = self;
    Clos { info, env: env.relocate(ar), body: ar.term(body.relocate(ar)) }
  }
}

impl<'a, 'b> Relocate<'a, Stack<'a, 'b>> for Stack<'_, 'b> {
  fn relocate(&self, ar: &'a Arena) -> Stack<'a, 'b> {
    match self {
      Stack::Nil => Stack::Nil,
      Stack::Cons { info, prev, value } => {
        Stack::Cons { info, prev: ar.frame(prev.relocate(ar)), value: value.relocate(ar) }
      }
    }
  }
}
