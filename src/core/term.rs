//! See: https://math.andrej.com/2012/11/29/how-to-implement-dependent-type-theory-iii/ (explicit substitutions)
//! See: https://github.com/bridgekat/leansubst/blob/main/Leansubst/Defs.lean (verified parallel substitutions)
//! See: https://github.com/bridgekat/calculus-of-constructions/blob/main/src/checker.lean (verified type assignment)

use bumpalo::Bump;
use std::cmp::max;

use self::Subs::*;
use self::Term::*;
use super::*;

/// Universes.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Sort(pub usize);

/// Preterms.
#[derive(Debug, Clone, Copy, Hash)]
pub enum Term<'a> {
  Univ(Sort),
  Var(usize),
  App(&'a Term<'a>, &'a Term<'a>),
  Lam(&'a Term<'a>, &'a Term<'a>),
  Pi(&'a Term<'a>, &'a Term<'a>),
  // Let(&'a Term<'a>, &'a Term<'a>),
  ES(&'a Term<'a>, &'a Subs<'a>),
}

/// Explicit substitutions.
#[derive(Debug, Clone, Copy, Hash)]
pub enum Subs<'a> {
  Shift(usize),
  Cons(&'a Term<'a>, &'a Subs<'a>),
}

/// Typing contexts: lists of `(type, definition?)`.
pub type Context<'a> = Vec<(&'a Term<'a>, Option<&'a Term<'a>>)>;

impl Sort {
  /// Universe formation rule.
  pub fn univ_rule(u: Sort) -> Option<Sort> {
    let Sort(u) = u;
    match u < 2 {
      true => Some(Sort(u + 1)),
      _ => None,
    }
  }

  /// Function type formation rule.
  pub fn pi_rule(u: Sort, v: Sort) -> Option<Sort> {
    let (Sort(u), Sort(v)) = (u, v);
    match u == 0 || v == 0 {
      true => Some(Sort(0)),
      _ => Some(Sort(max(u, v))),
    }
  }
}

impl<'a> Eq for Term<'a> {}
impl<'a> PartialEq for Term<'a> {
  /// Syntactical equality.
  fn eq(&self, other: &Self) -> bool {
    if std::ptr::eq(self, other) {
      return true;
    }
    match (self, other) {
      (Univ(u), Univ(v)) => u == v,
      (Var(i), Var(j)) => i == j,
      (App(f, x), App(g, y)) => f == g && x == y,
      (Lam(s, x), Lam(t, y)) => s == t && x == y,
      (Pi(q, r), Pi(s, t)) => q == s && r == t,
      // (Let(v, x), Let(w, y)) => v == w && x == y,
      (ES(x, s), ES(y, t)) => x == y && s == t,
      _ => false,
    }
  }
}

impl<'a> Eq for Subs<'a> {}
impl<'a> PartialEq for Subs<'a> {
  /// Syntactical equality.
  fn eq(&self, other: &Self) -> bool {
    if std::ptr::eq(self, other) {
      return true;
    }
    match (self, other) {
      (Shift(n), Shift(m)) => n == m,
      (Cons(x, s), Cons(y, t)) => x == y && s == t,
      _ => false,
    }
  }
}

impl<'a> Subs<'a> {
  /// Returns the `i`-th entry.
  pub fn get(mut self: &'a Self, mut i: usize) -> Term<'a> {
    loop {
      match *self {
        Shift(n) => return Var(i + n),
        Cons(x, s) => match i {
          0 => return *x,
          _ => (self, i) = (s, i - 1),
        },
      }
    }
  }

  /// Returns composition of `self` and `other`.
  pub fn then(&'a self, other: &'a Self, pool: &'a Bump) -> &'a Self {
    match (self, other) {
      (_, Shift(0)) => self,
      (Shift(0), _) => other,
      (Shift(n), Shift(m)) => pool.alloc(Shift(n + m)),
      (Shift(n), Cons(_, s)) => pool.alloc(Shift(n - 1)).then(s, pool),
      (Cons(x, s), _) => pool.alloc(Cons(pool.alloc(ES(x, other)), s.then(other, pool))),
    }
  }

  /// Transforms `self` for entering a binder.
  pub fn up(&'a self, pool: &'a Bump) -> &'a Self {
    pool.alloc(Cons(pool.alloc(Var(0)), self.then(&Shift(1), pool)))
  }
}

impl<'a> Term<'a> {
  /// Applies an explicit substitution (single step).
  pub fn apply(self, subs: &'a Subs, pool: &'a Bump) -> Self {
    match self {
      Univ(_) => self,
      Var(i) => subs.get(i),
      App(f, z) => App(pool.alloc(ES(f, subs)), pool.alloc(ES(z, subs))),
      Lam(t, z) => Lam(pool.alloc(ES(t, subs)), pool.alloc(ES(z, subs.up(pool)))),
      Pi(s, t) => Lam(pool.alloc(ES(s, subs)), pool.alloc(ES(t, subs.up(pool)))),
      ES(x, prev) => ES(x, prev.then(subs, pool)),
    }
  }

  /// Shifts free variables by `n` levels.
  pub fn shift(&'a self, n: usize, pool: &'a Bump) -> Self {
    ES(self, pool.alloc(Shift(n)))
  }

  /// Replaces free variable 0 by term `other` (e.g. while dropping the outermost layer of binder).
  pub fn subst(&'a self, other: &'a Self, pool: &'a Bump) -> Self {
    ES(self, pool.alloc(Cons(other, pool.alloc(Shift(0)))))
  }

  /// Applies explicit substitutions in well-typed `self` to obtain weak head normal form, unfolding definitions.
  /// By metatheory of the calculus of constructions, beta-reductions do not change type.
  pub fn whnf(mut self, ctx: &Context<'a>, pool: &'a Bump) -> Self {
    loop {
      match self {
        Var(i) => match ctx.get(ctx.len() - 1 - i) {
          Some((_, Some(v))) => self = v.shift(i + 1, pool),
          _ => return self,
        },
        App(x, y) => match x.whnf(ctx, pool) {
          Lam(_, z) => self = z.subst(y, pool),
          xx => return App(pool.alloc(xx), y),
        },
        ES(x, s) => self = x.apply(s, pool),
        _ => return self,
      }
    }
  }

  /// Given well-typed `self` and context `ctx`, tries conversion into [`Term::Univ`].
  pub fn as_univ(self, ctx: &Context<'a>, pool: &'a Bump) -> Option<Sort> {
    match self {
      Univ(u) => Some(u),
      _ => match self.whnf(ctx, pool) {
        Univ(u) => Some(u),
        _ => None,
      },
    }
  }

  /// Given well-typed `self` and context `ctx`, tries conversion into [`Term::Pi`].
  pub fn as_pi(self, ctx: &Context<'a>, pool: &'a Bump) -> Option<(&'a Self, &'a Self)> {
    match self {
      Pi(s, t) => Some((s, t)),
      _ => match self.whnf(ctx, pool) {
        Pi(s, t) => Some((s, t)),
        _ => None,
      },
    }
  }

  /// Given well-typed `self`, `other` and context `ctx`, returns if they are beta-convertible.
  pub fn conv(mut self, mut other: Self, ctx: &Context<'a>, pool: &'a Bump) -> bool {
    if self == other {
      return true;
    }
    (self, other) = (self.whnf(ctx, pool), other.whnf(ctx, pool));
    loop {
      match (self, other) {
        (Univ(u), Univ(v)) => return u == v,
        (Var(i), Var(j)) => return i == j,
        (App(f, x), App(g, y)) if x.conv(*y, ctx, pool) => (self, other) = (*f, *g),
        (App(_, _), App(_, _)) => return false,
        (Lam(s, x), Lam(t, y)) => return s.conv(*t, ctx, pool) && x.conv(*y, ctx, pool),
        (Pi(q, r), Pi(s, t)) => return q.conv(*s, ctx, pool) && r.conv(*t, ctx, pool),
        _ => return false,
      };
    }
  }

  /// Given preterm `self` and context `ctx`, returns the type of `self`.
  pub fn assign_type(self, ctx: &mut Context<'a>, pool: &'a Bump) -> Result<Self, Error> {
    match self {
      Univ(u) => {
        let v = Sort::univ_rule(u).ok_or(Error::UniverseOverflow)?;
        Ok(Univ(v))
      }
      Var(i) => {
        let (t, _) = ctx.get(ctx.len() - 1 - i).ok_or(Error::VariableOverflow)?;
        Ok(t.shift(i + 1, pool))
      }
      App(f, x) => {
        let ft = f.assign_type(ctx, pool)?;
        let (s, t) = ft.as_pi(ctx, pool).ok_or(Error::FunctionExpected)?;
        let xt = x.assign_type(ctx, pool)?;
        xt.conv(*s, ctx, pool).then_some(()).ok_or(Error::TypeMismatch)?;
        Ok(t.subst(x, pool))
      }
      Lam(t, x) => {
        let tt = t.assign_type(ctx, pool)?;
        let _ = tt.as_univ(ctx, pool).ok_or(Error::TypeExpected)?;
        ctx.push((t, None));
        let xt = x.assign_type(ctx, pool)?;
        ctx.pop();
        Ok(Pi(t, pool.alloc(xt)))
      }
      Pi(s, t) => {
        let st = s.assign_type(ctx, pool)?;
        let u = st.as_univ(ctx, pool).ok_or(Error::TypeExpected)?;
        ctx.push((s, None));
        let tt = t.assign_type(ctx, pool)?;
        let v = tt.as_univ(ctx, pool).ok_or(Error::TypeExpected)?;
        ctx.pop();
        let w = Sort::pi_rule(u, v).ok_or(Error::FunctionOverflow)?;
        Ok(Univ(w))
      }
      ES(x, s) => x.apply(s, pool).assign_type(ctx, pool),
    }
  }

  /// Given preterm `self` and context `ctx`, checks if `self` is type.
  pub fn is_type(self, ctx: &mut Context<'a>, pool: &'a Bump) -> Result<(), Error> {
    let t = self.assign_type(ctx, pool)?;
    t.as_univ(ctx, pool).map(|_| ()).ok_or(Error::TypeExpected)
  }

  /// Given preterms `self`, `ty` and context `ctx`, checks if `self` has type `ty`.
  pub fn check_type(self, ty: Self, ctx: &mut Context<'a>, pool: &'a Bump) -> Result<(), Error> {
    ty.is_type(ctx, pool)?;
    let t = self.assign_type(ctx, pool)?;
    t.conv(ty, ctx, pool).then_some(()).ok_or(Error::TypeMismatch)
  }
}
