//! See also: https://github.com/bridgekat/calculus-of-constructions/blob/main/src/checker.lean

use std::fmt::Display;
use typed_arena::Arena;

use self::Sort::*;
use self::Term::*;
use super::error::TypeError;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Sort {
  /// Universe of propositions.
  Prop,
  /// Universe of small types.
  Type,
  /// Universe of larger types.
  Kind,
}

impl Sort {
  pub fn pts_type(self: Sort) -> Option<Sort> {
    match self {
      Prop => Some(Type),
      Type => Some(Kind),
      Kind => None,
    }
  }

  pub fn pts_rule(u: Sort, v: Sort) -> Option<Sort> {
    match (u, v) {
      (Prop, Prop) | (Type, Prop) | (Kind, Prop) => Some(Prop),
      (Prop, Type) => None,
      (Prop, Kind) => None,
      (Type, Type) => Some(Type),
      (Type, Kind) | (Kind, Type) | (Kind, Kind) => Some(Kind),
    }
  }
}

#[derive(Debug, Clone, Copy)]
pub enum Term<'a> {
  /// Universes.
  Sort(Sort),
  /// Variables in de Bruijn indices.
  Var(usize),
  /// Function applications.
  App(&'a Term<'a>, &'a Term<'a>),
  /// Function descriptions.
  Lam(&'a Term<'a>, &'a Term<'a>),
  /// Function types.
  Pi(&'a Term<'a>, &'a Term<'a>),
  /// Definitions.
  Let(&'a Term<'a>, &'a Term<'a>),
}

impl<'a> Term<'a> {
  /// Move the term to a given pool.
  pub fn clone_to<'b>(&'a self, pool: &'b Arena<Term<'b>>) -> &'b Term<'b> {
    match *self {
      Sort(u) => pool.alloc(Sort(u)),
      Var(i) => pool.alloc(Var(i)),
      App(f, x) => pool.alloc(App(f.clone_to(pool), x.clone_to(pool))),
      Lam(t, x) => pool.alloc(Lam(t.clone_to(pool), x.clone_to(pool))),
      Pi(s, t) => pool.alloc(Pi(s.clone_to(pool), t.clone_to(pool))),
      Let(v, x) => pool.alloc(Let(v.clone_to(pool), x.clone_to(pool))),
    }
  }

  /// Replaces all variables `x` with `g(n, x)`, where `n` is binder depth.
  pub fn map_vars(
    &'a self,
    n: usize,
    g: &impl Fn(usize, &'a Term<'a>) -> &'a Term<'a>,
    pool: &'a Arena<Term<'a>>,
  ) -> &'a Term<'a> {
    match *self {
      Sort(_) => self,
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

  /// Shift variables with level ≥ `n` by `m` levels.
  pub fn shift(&'a self, n: usize, m: usize, pool: &'a Arena<Term<'a>>) -> &'a Term<'a> {
    self.map_vars(
      n,
      &|n, x| match *x {
        Var(i) if i >= n => pool.alloc(Var(i + m)),
        _ => x,
      },
      pool,
    )
  }

  /// Replace all variables at level = `n` by a term `y` (while deleting the outermost layer of binder).
  pub fn subst(&'a self, n: usize, y: &'a Term<'a>, pool: &'a Arena<Term<'a>>) -> &'a Term<'a> {
    self.map_vars(
      n,
      &|n, x| match *x {
        Var(i) if i > n => pool.alloc(Var(i - 1)),
        Var(i) if i == n => y.shift(0, n, pool),
        _ => x,
      },
      pool,
    )
  }

  /// Reads entry from context at reversed index `i`.
  pub fn try_ctx_entry<T: Copy>(ctx: &[T], i: usize) -> Option<T> {
    if i < ctx.len() {
      Some(ctx[ctx.len() - 1 - i])
    } else {
      None
    }
  }

  /// Beta-reduces well-typed `self` to weak head normal form, unfolding definitions at head.
  /// By metatheory of the calculus of constructions, beta-reductions do not change type.
  pub fn whnf(
    mut self: &'a Self,
    ctx: &[(&'a Term<'a>, Option<&'a Term<'a>>)],
    pool: &'a Arena<Term<'a>>,
  ) -> &'a Term<'a> {
    loop {
      match *self {
        App(x, y) => match x.whnf(ctx, pool) {
          Lam(_, x) => self = x.subst(0, y, pool),
          xx => return if std::ptr::eq(xx, x) { self } else { pool.alloc(App(xx, y)) },
        },
        Let(v, x) => self = x.subst(0, v, pool),
        Var(i) => match Self::try_ctx_entry(ctx, i) {
          Some((_, Some(v))) => self = v.shift(0, i + 1, pool),
          _ => return self,
        },
        _ => return self,
      }
    }
  }

  /// Given well-typed `self` and a list `ctx` of (_, definition?), tries conversion into [`Term::Sort`].
  pub fn try_as_sort(
    &'a self,
    ctx: &[(&'a Term<'a>, Option<&'a Term<'a>>)],
    pool: &'a Arena<Term<'a>>,
  ) -> Option<Sort> {
    match *self.whnf(ctx, pool) {
      Sort(u) => Some(u),
      _ => None,
    }
  }

  /// Given well-typed `self` and a list `ctx` of (_, definition?), tries conversion into [`Term::Pi`].
  pub fn try_as_pi(
    &'a self,
    ctx: &[(&'a Term<'a>, Option<&'a Term<'a>>)],
    pool: &'a Arena<Term<'a>>,
  ) -> Option<(&'a Term<'a>, &'a Term<'a>)> {
    match *self.whnf(ctx, pool) {
      Pi(s, t) => Some((s, t)),
      _ => None,
    }
  }

  /// Given well-typed `self` and `other`, and a list `ctx` of (_, definition?),
  /// returns if they are beta-convertible (definitionally equal).
  pub fn try_conv(
    &'a self,
    other: &'a Term<'a>,
    ctx: &Vec<(&'a Term<'a>, Option<&'a Term<'a>>)>,
    pool: &'a Arena<Term<'a>>,
  ) -> bool {
    match (*self.whnf(ctx, pool), *other.whnf(ctx, pool)) {
      (Sort(u), Sort(v)) => u == v,
      (Var(i), Var(j)) => i == j,
      (App(f, x), App(g, y)) => f.try_conv(g, ctx, pool) && x.try_conv(y, ctx, pool),
      (Lam(s, x), Lam(t, y)) => s.try_conv(t, ctx, pool) && x.try_conv(y, ctx, pool),
      (Pi(q, r), Pi(s, t)) => q.try_conv(s, ctx, pool) && r.try_conv(t, ctx, pool),
      _ => false,
    }
  }

  /// Given preterm `self` and a list `ctx` of (**type**, definition?), returns the type of `self`.
  pub fn infer_type(
    &'a self,
    ctx: &mut Vec<(&'a Term<'a>, Option<&'a Term<'a>>)>,
    pool: &'a Arena<Term<'a>>,
  ) -> Result<&'a Term<'a>, TypeError<'a>> {
    match *self {
      Sort(u) => {
        let v = u.pts_type().ok_or(TypeError::UniverseOverflow { term: self, sort: u })?;
        Ok(pool.alloc(Sort(v)))
      }
      Var(i) => {
        let entry = Self::try_ctx_entry(ctx, i);
        let (t, _) = entry.ok_or(TypeError::VariableOverflow { term: self, var: i, len: ctx.len() })?;
        Ok(t.shift(0, i + 1, pool))
      }
      App(f, x) => {
        let ft = f.infer_type(ctx, pool)?;
        let (s, t) = ft.try_as_pi(ctx, pool).ok_or(TypeError::FunctionExpected { term: f, ty: ft })?;
        let xt = x.infer_type(ctx, pool)?;
        xt.try_conv(s, ctx, pool).then_some(()).ok_or(TypeError::TypeMismatch { term: x, ty: xt, expect: s })?;
        Ok(t.subst(0, x, pool))
      }
      Lam(t, x) => {
        let tt = t.infer_type(ctx, pool)?;
        let _ = tt.try_as_sort(ctx, pool).ok_or(TypeError::TypeExpected { term: t, ty: tt })?;
        ctx.push((t, None));
        let xt = x.infer_type(ctx, pool)?;
        ctx.pop();
        Ok(pool.alloc(Pi(t, xt)))
      }
      Pi(s, t) => {
        let st = s.infer_type(ctx, pool)?;
        let u = st.try_as_sort(ctx, pool).ok_or(TypeError::TypeExpected { term: s, ty: st })?;
        ctx.push((s, None));
        let tt = t.infer_type(ctx, pool)?;
        let v = tt.try_as_sort(ctx, pool).ok_or(TypeError::TypeExpected { term: t, ty: tt })?;
        ctx.pop();
        let w = Sort::pts_rule(u, v).ok_or(TypeError::FunctionOverflow { term: self, from: u, to: v })?;
        Ok(pool.alloc(Sort(w)))
      }
      Let(v, x) => {
        let vt = v.infer_type(ctx, pool)?;
        ctx.push((vt, Some(v)));
        let xt = x.infer_type(ctx, pool)?;
        ctx.pop();
        Ok(xt.subst(0, v, pool))
      }
    }
  }
}

impl Display for Sort {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Prop => write!(f, "Prop"),
      Type => write!(f, "Type"),
      Kind => write!(f, "Kind"),
    }
  }
}

impl<'a> Display for Term<'a> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.fmt(&mut 0, &mut Vec::new(), 0, f)
  }
}

impl<'a> Term<'a> {
  /// Generate a variable name based on number `n`.
  fn name(mut n: usize) -> String {
    let mut len = 0;
    let mut m = 1;
    loop {
      len += 1;
      m *= 26;
      if n >= m {
        n -= m;
      } else {
        break;
      }
    }
    let mut res = String::new();
    for _ in 0..len {
      res.insert(0, ((n % 26) as u8 + b'a') as char);
      n /= 26;
    }
    res
  }

  /// Simple pretty-printer for debugging purposes.
  fn fmt(
    &self,
    count: &mut usize,
    ctx: &mut Vec<usize>,
    prec: usize,
    f: &mut std::fmt::Formatter<'_>,
  ) -> std::fmt::Result {
    match *self {
      Sort(u) => write!(f, "{u}"),
      Var(i) => match Self::try_ctx_entry(ctx, i) {
        Some(n) => write!(f, "{}", Self::name(n)),
        None => write!(f, "@{}", i - ctx.len()),
      },
      App(g, x) => {
        if prec > 3 {
          write!(f, "(")?;
        }
        g.fmt(count, ctx, 3, f)?;
        write!(f, " ")?;
        x.fmt(count, ctx, 4, f)?;
        if prec > 3 {
          write!(f, ")")?;
        }
        Ok(())
      }
      Lam(t, x) => {
        if prec > 1 {
          write!(f, "(")?;
        }
        write!(f, "fn ({} : ", Self::name(*count))?;
        t.fmt(count, ctx, 2, f)?;
        write!(f, ") => ")?;
        ctx.push(*count);
        *count += 1;
        x.fmt(count, ctx, 1, f)?;
        ctx.pop();
        if prec > 1 {
          write!(f, ")")?;
        }
        Ok(())
      }
      Pi(s, t) => {
        if prec > 2 {
          write!(f, "(")?;
        }
        write!(f, "({} : ", Self::name(*count))?;
        s.fmt(count, ctx, 2, f)?;
        write!(f, ") -> ")?;
        ctx.push(*count);
        *count += 1;
        t.fmt(count, ctx, 2, f)?;
        ctx.pop();
        if prec > 2 {
          write!(f, ")")?;
        }
        Ok(())
      }
      Let(v, x) => {
        if prec > 1 {
          write!(f, "(")?;
        }
        write!(f, "let {} = ", Self::name(*count))?;
        v.fmt(count, ctx, 2, f)?;
        write!(f, " in ")?;
        ctx.push(*count);
        *count += 1;
        x.fmt(count, ctx, 1, f)?;
        ctx.pop();
        if prec > 1 {
          write!(f, ")")?;
        }
        Ok(())
      }
    }
  }
}
