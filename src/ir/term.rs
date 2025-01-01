use std::slice::from_raw_parts;

use super::*;
use crate::arena::Arena;

/// # Binder information
///
/// Auxiliary information for bound variables (e.g. names, attributes).
#[derive(Debug, Clone, Copy)]
pub struct Bound<'a> {
  pub name: &'a str,
  pub attrs: &'a [&'a str],
}

/// # Field information
///
/// Auxiliary information for field variables (e.g. names, attributes).
#[derive(Debug, Clone, Copy)]
pub struct Field<'a> {
  pub name: &'a str,
  pub attrs: &'a [&'a str],
}

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
  /// Let expressions (binder info, value, *body*).
  Let(Bound<'a>, &'a Term<'a>, &'a Term<'a>),
  /// Function types (binder info, parameter type, *return type*).
  Pi(Bound<'a>, &'a Term<'a>, &'a Term<'a>),
  /// Function abstractions (binder info, *body*).
  Fun(Bound<'a>, &'a Term<'a>),
  /// Function applications (function, argument, dot-syntax flag).
  App(&'a Term<'a>, &'a Term<'a>, bool),
  /// Tuple types (field info, initial types, *last type*).
  Sig(Field<'a>, &'a Term<'a>, &'a Term<'a>),
  /// Tuple constructors (field info, initial values, *last value*).
  Tup(Field<'a>, &'a Term<'a>, &'a Term<'a>),
  /// Tuple initial segments (truncation, tuple).
  Init(usize, &'a Term<'a>),
  /// Tuple last element (tuple).
  Last(&'a Term<'a>),
  /// Empty tuple types.
  Unit,
  /// Empty tuple constructors.
  Star,
  /// Holes in unique identifiers.
  Meta(usize),
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
  /// Holes (environment, id).
  Meta(&'a Stack<'a, 'b>, usize),
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
  Cons { prev: &'a Stack<'a, 'b>, value: Val<'a, 'b> },
}

impl<'a, 'b> Stack<'a, 'b> {
  /// Creates an empty stack.
  pub fn new(_: &'a Arena) -> Self {
    Stack::Nil
  }

  /// Returns if the stack is empty.
  pub fn is_empty(&self) -> bool {
    match self {
      Stack::Nil => true,
      Stack::Cons { prev: _, value: _ } => false,
    }
  }

  /// Returns the length of the stack.
  pub fn len(&self) -> usize {
    let mut curr = self;
    let mut len = 0;
    while let Stack::Cons { prev, value: _ } = curr {
      len += 1;
      curr = prev;
    }
    len
  }

  /// Returns the value at the given de Bruijn index, if it exists.
  pub fn get(&self, index: usize, ar: &'a Arena) -> Option<Val<'a, 'b>> {
    let mut curr = self;
    let mut index = index;
    ar.inc_lookup_count();
    while let Stack::Cons { prev, value } = curr {
      ar.inc_link_count();
      if index == 0 {
        return Some(*value);
      }
      index -= 1;
      curr = prev;
    }
    None
  }

  /// Extends the stack with a new value.
  pub fn extend(&self, value: Val<'a, 'b>, ar: &'a Arena) -> Self {
    Stack::Cons { prev: ar.frame(*self), value }
  }
}

impl Bound<'_> {
  /// Clones `self` to given arena.
  pub fn relocate<'b>(&self, ar: &'b Arena) -> Bound<'b> {
    Bound { name: ar.string(self.name), attrs: ar.strings(self.attrs) }
  }
}

impl Field<'_> {
  /// Clones `self` to given arena.
  pub fn relocate<'b>(&self, ar: &'b Arena) -> Field<'b> {
    Field { name: ar.string(self.name), attrs: ar.strings(self.attrs) }
  }
}

impl Term<'_> {
  /// Clones `self` to given arena.
  pub fn relocate<'b>(&self, ar: &'b Arena) -> &'b Term<'b> {
    match self {
      Term::Univ(v) => ar.term(Term::Univ(*v)),
      Term::Var(ix) => ar.term(Term::Var(*ix)),
      Term::Ann(x, t, b) => ar.term(Term::Ann(x.relocate(ar), t.relocate(ar), *b)),
      Term::Let(i, v, x) => ar.term(Term::Let(i.relocate(ar), v.relocate(ar), x.relocate(ar))),
      Term::Pi(i, t, u) => ar.term(Term::Pi(i.relocate(ar), t.relocate(ar), u.relocate(ar))),
      Term::Fun(i, b) => ar.term(Term::Fun(i.relocate(ar), b.relocate(ar))),
      Term::App(f, x, b) => ar.term(Term::App(f.relocate(ar), x.relocate(ar), *b)),
      Term::Sig(i, t, u) => ar.term(Term::Sig(i.relocate(ar), t.relocate(ar), u.relocate(ar))),
      Term::Tup(i, a, b) => ar.term(Term::Tup(i.relocate(ar), a.relocate(ar), b.relocate(ar))),
      Term::Init(n, x) => ar.term(Term::Init(*n, x.relocate(ar))),
      Term::Last(x) => ar.term(Term::Last(x.relocate(ar))),
      Term::Unit => ar.term(Term::Unit),
      Term::Star => ar.term(Term::Star),
      Term::Meta(m) => ar.term(Term::Meta(*m)),
    }
  }
}

impl<'b> Term<'b> {
  /// Reduces `self` so that all `let`s are collected into the environment and then frozen at
  /// binders. This is mutually recursive with [`Clos::apply`], forming an eval-apply loop.
  ///
  /// Pre-conditions:
  ///
  /// - `self` is well-typed under a context and environment `env` (to ensure termination).
  pub fn eval<'a>(&self, env: &Stack<'a, 'b>, ar: &'b Arena) -> Result<Val<'a, 'b>, EvalError<'b>> {
    match self {
      // Universes are already in normal form.
      Term::Univ(v) => Ok(Val::Univ(*v)),
      // The (δ) rule is always applied.
      // Variables of values are in de Bruijn levels, so weakening is no-op.
      Term::Var(ix) => env.get(*ix, ar).ok_or_else(|| EvalError::env_index(*ix, env.len())),
      // The (τ) rule is always applied.
      Term::Ann(x, _, _) => x.eval(env, ar),
      // For `let`s, we reduce the value, collect it into the environment to reduce the body.
      Term::Let(_, v, x) => x.eval(&env.extend(v.eval(env, ar)?, ar), ar),
      // For binders, we freeze the whole environment and store the body as a closure.
      Term::Pi(_, t, u) => Ok(Val::Pi(ar.val(t.eval(env, ar)?), ar.clos(Clos { env: *env, body: u }))),
      Term::Fun(_, b) => Ok(Val::Fun(ar.clos(Clos { env: *env, body: b }))),
      // For applications, we reduce both operands and combine them back.
      // In the case of a redex, the (β) rule is applied.
      Term::App(f, x, _) => match (f.eval(env, ar)?, x.eval(env, ar)?) {
        (Val::Fun(b), x) => b.apply(x, ar),
        (f, x) => Ok(Val::App(ar.val(f), ar.val(x))),
      },
      // For binders, we freeze the whole environment and store the body as a closure.
      Term::Unit | Term::Sig(_, _, _) => {
        let mut init = self;
        let mut us = Vec::new();
        while let Term::Sig(_, t, u) = init {
          init = t;
          us.push(Clos { env: *env, body: u });
        }
        if let Term::Unit = init {
          us.reverse();
          Ok(Val::Sig(ar.closures(&us)))
        } else {
          Err(EvalError::sig_improper(ar.term(*self)))
        }
      }
      Term::Star | Term::Tup(_, _, _) => {
        let mut init = self;
        let mut bs = Vec::new();
        while let Term::Tup(_, a, b) = init {
          init = a;
          bs.push(b);
        }
        if let Term::Star = init {
          bs.reverse();
          // Eagerly evaluate tuple elements.
          let vs = ar.values(bs.len(), Val::Gen(0));
          for (i, b) in bs.iter().enumerate() {
            // SAFETY: the borrowed range `&vs[..i]` is no longer modified.
            let a = Val::Tup(unsafe { from_raw_parts(vs.as_ptr(), i) });
            vs[i] = b.eval(&env.extend(a, ar), ar)?;
          }
          Ok(Val::Tup(vs))
        } else {
          Err(EvalError::tup_improper(ar.term(*self)))
        }
      }
      // For initials (i.e. iterated first projections), we reduce the operand and combine it back.
      // In the case of a redex, the (π init) rule is applied.
      Term::Init(n, x) => match x.eval(env, ar)? {
        Val::Init(m, y) => Ok(Val::Init(n + m, y)),
        Val::Tup(bs) => {
          let m = bs.len().checked_sub(*n).ok_or_else(|| EvalError::tup_init(*n, bs.len()))?;
          Ok(Val::Tup(&bs[..m]))
        }
        a => Ok(Val::Init(*n, ar.val(a))),
      },
      // For lasts (i.e. second projections), we reduce the operand and combine it back.
      // In the case of a redex, the (π last) rule is applied.
      Term::Last(x) => match x.eval(env, ar)? {
        Val::Tup(bs) => {
          let i = bs.len().checked_sub(1).ok_or_else(|| EvalError::tup_last(1, bs.len()))?;
          Ok(bs[i])
        }
        a => Ok(Val::Last(ar.val(a))),
      },
      // For holes, we freeze the whole environment around it.
      Term::Meta(m) => Ok(Val::Meta(ar.frame(*env), *m)),
    }
  }
}

impl<'a, 'b> Clos<'a, 'b> {
  /// Inserts a new `let` around the body after the frozen `let`s, and reduces the body under the
  /// empty environment populated with all `let`s. This is mutually recursive with [`Term::eval`],
  /// forming an eval-apply loop.
  pub fn apply(&self, x: Val<'a, 'b>, ar: &'b Arena) -> Result<Val<'a, 'b>, EvalError<'b>> {
    let Self { env, body } = self;
    body.eval(&env.extend(x, ar), ar)
  }
}

impl<'b> Val<'_, 'b> {
  /// Returns if `self` and `other` are definitionally equal. Can be an expensive operation if
  /// they are indeed definitionally equal.
  ///
  /// Pre-conditions:
  ///
  /// - `self` and `other` are well-typed under a context with size `len` (to ensure termination).
  pub fn conv(&self, other: &Self, len: usize, ar: &'b Arena) -> Result<bool, EvalError<'b>> {
    match (self, other) {
      (Val::Univ(v), Val::Univ(w)) => Ok(v == w),
      (Val::Gen(i), Val::Gen(j)) => Ok(i == j),
      (Val::Pi(t, v), Val::Pi(u, w)) => Ok(
        Val::conv(t, u, len, ar)?
          && Val::conv(&v.apply(Val::Gen(len), ar)?, &w.apply(Val::Gen(len), ar)?, len + 1, ar)?,
      ),
      (Val::Fun(b), Val::Fun(c)) => {
        Ok(Val::conv(&b.apply(Val::Gen(len), ar)?, &c.apply(Val::Gen(len), ar)?, len + 1, ar)?)
      }
      (Val::App(f, x), Val::App(g, y)) => Ok(Val::conv(f, g, len, ar)? && Val::conv(x, y, len, ar)?),
      (Val::Sig(us), Val::Sig(vs)) if us.len() == vs.len() => {
        for (u, v) in us.iter().zip(vs.iter()) {
          if !Val::conv(&u.apply(Val::Gen(len), ar)?, &v.apply(Val::Gen(len), ar)?, len + 1, ar)? {
            return Ok(false);
          }
        }
        Ok(true)
      }
      (Val::Tup(bs), Val::Tup(cs)) if bs.len() == cs.len() => {
        for (b, c) in bs.iter().zip(cs.iter()) {
          if !Val::conv(b, c, len, ar)? {
            return Ok(false);
          }
        }
        Ok(true)
      }
      (Val::Init(n, x), Val::Init(m, y)) => Ok(n == m && Val::conv(x, y, len, ar)?),
      (Val::Last(x), Val::Last(y)) => Ok(Val::conv(x, y, len, ar)?),
      _ => Ok(false),
    }
  }
}
