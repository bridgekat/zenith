use typed_arena::Arena;

use self::Term::*;
use super::*;
use crate::core;

/// Preterms.
#[derive(Debug, Clone, Copy, Hash)]
pub enum Term<'a> {
  /// Universes.
  Univ(Sort),

  /// Variables in de Bruijn indices.
  Var(usize),

  /// Function applications.
  App(&'a Term<'a>, &'a Term<'a>),

  /// Function descriptions.
  Lam(&'a Term<'a>, &'a Term<'a>, BinderInfo),

  /// Function types.
  Pi(&'a Term<'a>, &'a Term<'a>, BinderInfo),

  /// Metavariables.
  Meta(usize),

  /// Definitions.
  Let(&'a Term<'a>, &'a Term<'a>, &'a Term<'a>, BinderInfo),

  /// Type annotations.
  Ty(&'a Term<'a>, &'a Term<'a>),

  /// Source info.
  Src(&'a Term<'a>, SourceInfo),
}

/// Dictionary index and implicitness of the bound variable.
#[derive(Debug, Clone, Copy, Hash)]
pub struct BinderInfo {
  pub name_id: usize,
  pub is_implicit: bool,
}

/// Starting and ending positions in input source code.
#[derive(Debug, Clone, Copy, Hash)]
pub struct SourceInfo {
  pub begin: usize,
  pub end: usize,
}

impl<'a> Eq for Term<'a> {}
impl<'a> PartialEq for Term<'a> {
  /// Syntactical equality modulo alpha conversion.
  fn eq(&self, other: &Self) -> bool {
    if std::ptr::eq(self, other) {
      return true;
    }
    match (self, other) {
      (Self::Univ(u), Self::Univ(v)) => u == v,
      (Self::Var(i), Self::Var(j)) => i == j,
      (Self::App(f, x), Self::App(g, y)) => f == g && x == y,
      (Self::Lam(s, x, _), Self::Lam(t, y, _)) => s == t && x == y,
      (Self::Pi(q, r, _), Self::Pi(s, t, _)) => q == s && r == t,
      (Self::Meta(i), Self::Meta(j)) => i == j,
      (Self::Let(s, v, x, _), Self::Let(t, w, y, _)) => s == t && v == w && x == y,
      (Self::Ty(x, s), Self::Ty(y, t)) => x == y && s == t,
      (Self::Src(x, _), Self::Src(y, _)) => x == y,
      _ => false,
    }
  }
}

impl<'a> Term<'a> {
  /// Moves the term to a given pool.
  pub fn clone_to<'b>(&'a self, pool: &'b Arena<Term<'b>>) -> &'b Term<'b> {
    match *self {
      Univ(u) => pool.alloc(Univ(u)),
      Var(i) => pool.alloc(Var(i)),
      App(f, x) => pool.alloc(App(f.clone_to(pool), x.clone_to(pool))),
      Lam(t, x, info) => pool.alloc(Lam(t.clone_to(pool), x.clone_to(pool), info)),
      Pi(s, t, info) => pool.alloc(Pi(s.clone_to(pool), t.clone_to(pool), info)),
      Meta(i) => pool.alloc(Meta(i)),
      Let(t, v, x, info) => pool.alloc(Let(t.clone_to(pool), v.clone_to(pool), x.clone_to(pool), info)),
      Ty(x, t) => pool.alloc(Ty(x.clone_to(pool), t.clone_to(pool))),
      Src(x, info) => pool.alloc(Src(x.clone_to(pool), info)),
    }
  }

  /// Converts the term to core term.
  pub fn clone_to_core<'b>(&'a self, pool: &'b Arena<core::Term<'b>>) -> Result<&'b core::Term<'b>, Error> {
    match *self {
      Univ(Sort(u)) => Ok(pool.alloc(core::Term::Univ(core::Sort(u)))),
      Var(i) => Ok(pool.alloc(core::Term::Var(i))),
      App(f, x) => Ok(pool.alloc(core::Term::App(f.clone_to_core(pool)?, x.clone_to_core(pool)?))),
      Lam(t, x, _) => Ok(pool.alloc(core::Term::Lam(t.clone_to_core(pool)?, x.clone_to_core(pool)?))),
      Pi(s, t, _) => Ok(pool.alloc(core::Term::Pi(s.clone_to_core(pool)?, t.clone_to_core(pool)?))),
      Meta(_) => Err(Error::UnresolvedMeta { term: self }),
      Let(_, v, x, _) => Ok(pool.alloc(core::Term::Let(v.clone_to_core(pool)?, x.clone_to_core(pool)?))),
      Ty(x, _) => Ok(x.clone_to_core(pool)?),
      Src(x, _) => Ok(x.clone_to_core(pool)?),
    }
  }

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
      Lam(t, x, info) => {
        let tt = t.map_vars(n, g, pool);
        let xx = x.map_vars(n + 1, g, pool);
        return if std::ptr::eq(tt, t) && std::ptr::eq(xx, x) { self } else { pool.alloc(Lam(tt, xx, info)) };
      }
      Pi(s, t, info) => {
        let ss = s.map_vars(n, g, pool);
        let tt = t.map_vars(n + 1, g, pool);
        return if std::ptr::eq(ss, s) && std::ptr::eq(tt, t) { self } else { pool.alloc(Pi(ss, tt, info)) };
      }
      Meta(_) => self,
      Let(t, v, x, info) => {
        let tt = t.map_vars(n, g, pool);
        let vv = v.map_vars(n, g, pool);
        let xx = x.map_vars(n + 1, g, pool);
        return if std::ptr::eq(vv, v) && std::ptr::eq(xx, x) { self } else { pool.alloc(Let(tt, vv, xx, info)) };
      }
      Ty(x, t) => {
        let xx = x.map_vars(n, g, pool);
        let tt = t.map_vars(n, g, pool);
        return if std::ptr::eq(xx, x) && std::ptr::eq(tt, t) { self } else { pool.alloc(Ty(xx, tt)) };
      }
      Src(x, info) => {
        let xx = x.map_vars(n, g, pool);
        return if std::ptr::eq(xx, x) { self } else { pool.alloc(Src(xx, info)) };
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

  /// Beta-reduces `self` to weak head normal form, optionally unfolding definitions at head.
  pub fn whnf(mut self: &'a Self, unfold: bool, ctx: &Context<'a>, pool: &'a Arena<Self>) -> &'a Self {
    loop {
      match *self {
        Var(i) => match ctx.var_def(i, pool) {
          Some(v) if unfold => self = v,
          _ => return self,
        },
        App(x, y) => match x.whnf(unfold, ctx, pool) {
          Lam(_, x, _) => self = x.subst(0, y, pool),
          xx => return if std::ptr::eq(xx, x) { self } else { pool.alloc(App(xx, y)) },
        },
        Let(_, v, x, _) => self = x.subst(0, v, pool),
        Ty(x, _) => self = x,
        Src(x, _) => self = x,
        _ => return self,
      }
    }
  }

  /// Given well-typed `self` and context `ctx`, tries conversion into [`Term::Univ`].
  pub fn as_univ(&'a self, ctx: &Context<'a>, pool: &'a Arena<Self>) -> Option<Sort> {
    match *self {
      Univ(u) => Some(u),
      _ => match *self.whnf(true, ctx, pool) {
        Univ(u) => Some(u),
        _ => None,
      },
    }
  }

  /// Given well-typed `self` and context `ctx`, tries conversion into [`Term::Pi`].
  pub fn as_pi(&'a self, ctx: &Context<'a>, pool: &'a Arena<Self>) -> Option<(&'a Self, &'a Self)> {
    match *self {
      Pi(s, t, _) => Some((s, t)),
      _ => match *self.whnf(true, ctx, pool) {
        Pi(s, t, _) => Some((s, t)),
        _ => None,
      },
    }
  }

  /*
  /// Given well-typed `self`, `other` and context `ctx`, returns if they are beta-convertible.
  pub fn conv(mut self: &'a Self, mut other: &'a Self, ctx: &Context<'a>, pool: &'a Arena<Self>) -> bool {
    if self.eq(other) {
      return true;
    }
    (self, other) = (self.whnf(true, ctx, pool), other.whnf(true, ctx, pool));
    loop {
      match (*self, *other) {
        (Univ(u), Univ(v)) => return u == v,
        (Var(i), Var(j)) => return i == j,
        (App(f, x), App(g, y)) if x.conv(y, ctx, pool) => (self, other) = (f, g),
        (App(_, _), App(_, _)) => return false,
        (Lam(s, x), Lam(t, y)) => return s.conv(t, ctx, pool) && x.conv(y, ctx, pool),
        (Pi(q, r), Pi(s, t)) => return q.conv(s, ctx, pool) && r.conv(t, ctx, pool),
        (Let(v, x), Let(w, y)) => return v.conv(w, ctx, pool) && x.conv(y, ctx, pool),
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
        let _ = tt.as_univ(ctx, pool).ok_or(Error::TypeExpected { term: t, ty: tt })?;
        ctx.push((t, None));
        let xt = x.assign_type(ctx, pool)?;
        ctx.pop();
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
  */
}
