//! See also: https://github.com/bridgekat/calculus-of-constructions/blob/main/src/checker.lean

use std::fmt::Display;
use typed_arena::Arena;

use self::Sort::*;
use self::Term::*;
use super::type_error::*;

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

  pub fn pts_rule(u: Sort, v: Sort) -> Sort {
    match (u, v) {
      (Prop, _) | (_, Prop) => Prop,
      (Kind, _) | (_, Kind) => Kind,
      (Type, Type) => Type,
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
}

impl<'a> Term<'a> {
  pub fn clone_to<'b>(&'a self, pool: &'b Arena<Term<'b>>) -> &'b Term<'b> {
    match *self {
      Sort(u) => pool.alloc(Sort(u)),
      Var(i) => pool.alloc(Var(i)),
      App(f, x) => pool.alloc(App(f.clone_to(pool), x.clone_to(pool))),
      Lam(t, x) => pool.alloc(Lam(t.clone_to(pool), x.clone_to(pool))),
      Pi(s, t) => pool.alloc(Pi(s.clone_to(pool), t.clone_to(pool))),
    }
  }

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

  /// Beta-reduce well-typed `self` to weak head normal form.
  /// By metatheory of the calculus of constructions, beta-reductions do not change type.
  pub fn whnf(&'a self, pool: &'a Arena<Term<'a>>) -> &'a Term<'a> {
    match *self {
      App(x, y) => match x.whnf(pool) {
        Lam(_, x) => x.subst(0, y, pool).whnf(pool),
        xx => return if std::ptr::eq(xx, x) { self } else { pool.alloc(App(xx, y)) },
      },
      _ => self,
    }
  }

  /// Given well-typed `self` and `other`, returns if they are beta-convertible (definitionally equal).
  pub fn conv(&'a self, other: &'a Term<'a>, pool: &'a Arena<Term<'a>>) -> bool {
    match (self.whnf(pool), other.whnf(pool)) {
      (Sort(u), Sort(v)) => u == v,
      (Var(i), Var(j)) => i == j,
      (App(f, x), App(g, y)) => f.conv(g, pool) && x.conv(y, pool),
      (Lam(s, x), Lam(t, y)) => s.conv(t, pool) && x.conv(y, pool),
      (Pi(q, r), Pi(s, t)) => q.conv(s, pool) && r.conv(t, pool),
      _ => false,
    }
  }

  /// Reads entry from context at reversed index `i`.
  fn rev_get<T: Copy>(ctx: &mut Vec<T>, i: usize) -> Option<T> {
    if i < ctx.len() {
      Some(ctx[ctx.len() - 1 - i])
    } else {
      None
    }
  }

  /// Given preterm `self` and a list `ctx` of **types**, returns the type of `self`.
  pub fn infer_type(
    &'a self,
    ctx: &mut Vec<&'a Term<'a>>,
    pool: &'a Arena<Term<'a>>,
  ) -> Result<&'a Term<'a>, TypeError<'a>> {
    match *self {
      Sort(u) => match u.pts_type() {
        Some(v) => Ok(pool.alloc(Sort(v))),
        None => Err(TypeError::UniverseOverflow { term: self, sort: u }),
      },
      Var(i) => match Self::rev_get(ctx, i) {
        Some(t) => Ok(t.shift(0, i + 1, pool)),
        None => Err(TypeError::VariableOverflow { term: self, var: i, len: ctx.len() }),
      },
      App(f, x) => match f.infer_type(ctx, pool)?.whnf(pool) {
        Pi(s, t) => match x.infer_type(ctx, pool)?.conv(s, pool) {
          true => Ok(t.subst(0, x, pool)),
          _ => Err(TypeError::TypeMismatch { term: x, ty: x.infer_type(ctx, pool)?, expect: s }),
        },
        other => Err(TypeError::FunctionExpected { term: f, ty: other }),
      },
      Lam(t, x) => match t.infer_type(ctx, pool)?.whnf(pool) {
        Sort(_) => {
          ctx.push(t);
          let res = pool.alloc(Pi(t, x.infer_type(ctx, pool)?));
          ctx.pop();
          Ok(res)
        }
        other => Err(TypeError::TypeExpected { term: t, ty: other }),
      },
      Pi(s, t) => match s.infer_type(ctx, pool)?.whnf(pool) {
        Sort(u) => {
          ctx.push(s);
          let res = match t.infer_type(ctx, pool)?.whnf(pool) {
            Sort(v) => Ok(pool.alloc(Sort(Sort::pts_rule(*u, *v)))),
            other => Err(TypeError::TypeExpected { term: t, ty: other }),
          }?;
          ctx.pop();
          Ok(res)
        }
        other => Err(TypeError::TypeExpected { term: s, ty: other }),
      },
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
      Var(i) => match Self::rev_get(ctx, i) {
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
    }
  }
}
