//! See: <https://github.com/bridgekat/calculus-of-constructions/blob/main/src/checker.lean>

use std::cmp::max;
use typed_arena::Arena;

use self::Term::*;
use super::*;

/// Universes.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Sort(pub usize);

/// Preterms.
#[derive(Debug, Clone, Copy)]
pub enum Term<'a> {
  Univ(Sort),
  Var(usize),
  App(&'a Term<'a>, &'a Term<'a>),
  Lam(&'a Term<'a>, &'a Term<'a>),
  Pi(&'a Term<'a>, &'a Term<'a>),
  Let(&'a Term<'a>, &'a Term<'a>),
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
    match v == 0 {
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
      (Let(v, x), Let(w, y)) => v == w && x == y,
      _ => false,
    }
  }
}

impl<'a> Term<'a> {
  /// Replaces all variables `x` with `g(n, x)`, where `n` is binder depth.
  pub fn map_vars(&'a self, n: usize, g: &impl Fn(usize, &'a Self) -> &'a Self, pool: &'a Arena<Self>) -> &'a Self {
    match *self {
      Univ(_) => self,
      Var(_) => g(n, self),
      App(f, x) => {
        let ff = f.map_vars(n, g, pool);
        let xx = x.map_vars(n, g, pool);
        return if std::ptr::eq(ff, f) && std::ptr::eq(xx, x) { self } else { pool.alloc(App(ff, xx)) };
      }
      Lam(t, x) => {
        let tt = t.map_vars(n, g, pool);
        let xx = x.map_vars(n + 1, g, pool);
        return if std::ptr::eq(tt, t) && std::ptr::eq(xx, x) { self } else { pool.alloc(Lam(tt, xx)) };
      }
      Pi(s, t) => {
        let ss = s.map_vars(n, g, pool);
        let tt = t.map_vars(n + 1, g, pool);
        return if std::ptr::eq(ss, s) && std::ptr::eq(tt, t) { self } else { pool.alloc(Pi(ss, tt)) };
      }
      Let(v, x) => {
        let vv = v.map_vars(n, g, pool);
        let xx = x.map_vars(n + 1, g, pool);
        return if std::ptr::eq(vv, v) && std::ptr::eq(xx, x) { self } else { pool.alloc(Let(vv, xx)) };
      }
    }
  }

  /// Shifts variables with level ≥ `n` by `m` levels.
  pub fn shift(&'a self, n: usize, m: usize, pool: &'a Arena<Self>) -> &'a Self {
    self.map_vars(
      n,
      &|n, x| match *x {
        Var(i) if i >= n => pool.alloc(Var(i + m)),
        _ => x,
      },
      pool,
    )
  }

  /// Replaces all variables at level = `n` by a term `other`.
  pub fn subst(&'a self, n: usize, other: &'a Self, pool: &'a Arena<Self>) -> &'a Self {
    self.map_vars(
      n,
      &|n, x| match *x {
        Var(i) if i > n => pool.alloc(Var(i - 1)),
        Var(i) if i == n => other.shift(0, n, pool),
        _ => x,
      },
      pool,
    )
  }

  /// Beta-reduces well-typed `self` to weak head normal form, unfolding definitions at head.
  /// By metatheory of the calculus of constructions, beta-reductions do not change type.
  pub fn whnf(mut self: &'a Self, ctx: &Context<'a>, pool: &'a Arena<Self>) -> &'a Self {
    loop {
      match *self {
        Var(i) => match ctx.get(ctx.len() - 1 - i) {
          Some((_, Some(v))) => self = v.shift(0, i + 1, pool),
          _ => return self,
        },
        App(x, y) => match x.whnf(ctx, pool) {
          Lam(_, z) => self = z.subst(0, y, pool),
          xx => return if std::ptr::eq(xx, x) { self } else { pool.alloc(App(xx, y)) },
        },
        Let(v, x) => self = x.subst(0, v, pool),
        _ => return self,
      }
    }
  }

  /// Given well-typed `self` and context `ctx`, tries conversion into [`Term::Univ`].
  pub fn as_univ(&'a self, ctx: &Context<'a>, pool: &'a Arena<Self>) -> Option<Sort> {
    match *self {
      Univ(u) => Some(u),
      _ => match *self.whnf(ctx, pool) {
        Univ(u) => Some(u),
        _ => None,
      },
    }
  }

  /// Given well-typed `self` and context `ctx`, tries conversion into [`Term::Pi`].
  pub fn as_pi(&'a self, ctx: &Context<'a>, pool: &'a Arena<Self>) -> Option<(&'a Self, &'a Self)> {
    match *self {
      Pi(s, t) => Some((s, t)),
      _ => match *self.whnf(ctx, pool) {
        Pi(s, t) => Some((s, t)),
        _ => None,
      },
    }
  }

  /// Given well-typed `self`, `other` and context `ctx`, returns if they are beta-convertible.
  pub fn conv(mut self: &'a Self, mut other: &'a Self, ctx: &Context<'a>, pool: &'a Arena<Self>) -> bool {
    if self.eq(other) {
      return true;
    }
    (self, other) = (self.whnf(ctx, pool), other.whnf(ctx, pool));
    loop {
      match (*self, *other) {
        (Univ(u), Univ(v)) => return u == v,
        (Var(i), Var(j)) => return i == j,
        (App(f, x), App(g, y)) if x.conv(y, ctx, pool) => (self, other) = (f, g),
        (Lam(s, x), Lam(t, y)) => return s.conv(t, ctx, pool) && x.conv(y, ctx, pool),
        (Pi(q, r), Pi(s, t)) => return q.conv(s, ctx, pool) && r.conv(t, ctx, pool),
        _ => return false,
      };
    }
  }

  /// Given preterm `self` and context `ctx`, returns the type of `self`.
  pub fn assign_type(&'a self, ctx: &mut Context<'a>, pool: &'a Arena<Self>) -> Result<&'a Self, Error> {
    match *self {
      Univ(u) => {
        let v = Sort::univ_rule(u).ok_or(Error::UniverseOverflow { univ: u })?;
        Ok(pool.alloc(Univ(v)))
      }
      Var(i) => {
        let (t, _) = ctx.get(ctx.len() - 1 - i).ok_or(Error::VariableOverflow { var: i, len: ctx.len() })?;
        Ok(t.shift(0, i + 1, pool))
      }
      App(f, x) => {
        let ft = f.assign_type(ctx, pool)?;
        let (s, t) = ft.as_pi(ctx, pool).ok_or(Error::FunctionExpected { term: f, ty: ft })?;
        let xt = x.assign_type(ctx, pool)?;
        xt.conv(s, ctx, pool).then_some(()).ok_or(Error::TypeMismatch { term: x, ty: xt, expect: s })?;
        Ok(t.subst(0, x, pool))
      }
      Lam(t, x) => {
        let tt = t.assign_type(ctx, pool)?;
        let u = tt.as_univ(ctx, pool).ok_or(Error::TypeExpected { term: t, ty: tt })?;
        ctx.push((t, None));
        let xt = x.assign_type(ctx, pool)?;
        let xtt = xt.assign_type(ctx, pool)?;
        let v = xtt.as_univ(ctx, pool).ok_or(Error::TypeExpected { term: xt, ty: xtt })?;
        ctx.pop();
        let _ = Sort::pi_rule(u, v).ok_or(Error::FunctionOverflow { from: u, to: v })?;
        Ok(pool.alloc(Pi(t, xt)))
      }
      Pi(s, t) => {
        let st = s.assign_type(ctx, pool)?;
        let u = st.as_univ(ctx, pool).ok_or(Error::TypeExpected { term: s, ty: st })?;
        ctx.push((s, None));
        let tt = t.assign_type(ctx, pool)?;
        let v = tt.as_univ(ctx, pool).ok_or(Error::TypeExpected { term: t, ty: tt })?;
        ctx.pop();
        let w = Sort::pi_rule(u, v).ok_or(Error::FunctionOverflow { from: u, to: v })?;
        Ok(pool.alloc(Univ(w)))
      }
      Let(v, x) => {
        let vt = v.assign_type(ctx, pool)?;
        ctx.push((vt, Some(v)));
        let xt = x.assign_type(ctx, pool)?;
        ctx.pop();
        Ok(xt.subst(0, v, pool))
      }
    }
  }

  /// Given preterm `self` and context `ctx`, checks if `self` is type.
  pub fn is_type(&'a self, ctx: &mut Context<'a>, pool: &'a Arena<Self>) -> Result<(), Error<'a>> {
    let t = self.assign_type(ctx, pool)?;
    t.as_univ(ctx, pool).map(|_| ()).ok_or(Error::TypeExpected { term: self, ty: t })
  }

  /// Given preterms `self`, `ty` and context `ctx`, checks if `self` has type `ty`.
  pub fn check_type(&'a self, ty: &'a Self, ctx: &mut Context<'a>, pool: &'a Arena<Self>) -> Result<(), Error<'a>> {
    ty.is_type(ctx, pool)?;
    let t = self.assign_type(ctx, pool)?;
    t.conv(ty, ctx, pool).then_some(()).ok_or(Error::TypeMismatch { term: self, ty: t, expect: ty })
  }
}
