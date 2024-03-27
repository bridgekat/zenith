use std::fmt::Display;

use self::Error::*;
use super::*;

#[derive(Debug, Clone, Copy)]
pub enum Error<'a> {
  UniverseOverflow { univ: Sort },
  FunctionOverflow { from: Sort, to: Sort },
  VariableOverflow { var: usize, len: usize },
  FunctionExpected { term: &'a Term<'a>, ty: &'a Term<'a> },
  TypeExpected { term: &'a Term<'a>, ty: &'a Term<'a> },
  TypeMismatch { term: &'a Term<'a>, ty: &'a Term<'a>, expect: &'a Term<'a> },
}

/// Simple pretty-printer for debugging purposes.
impl<'a> Display for Error<'a> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      UniverseOverflow { univ } => write!(f, "universe {univ} does not have a type"),
      FunctionOverflow { from, to } => write!(f, "dependent functions from {from} to {to} are unspecified"),
      VariableOverflow { var, len } => write!(f, "variable index {var} out of bound, context has size {len}"),
      FunctionExpected { term, ty } => write!(f, "function expected, term {term} has type {ty}, which is not Pi type"),
      TypeExpected { term, ty } => write!(f, "type expected, term {term} has type {ty}, which is not universe type"),
      TypeMismatch { term, ty, expect } => write!(f, "term {term} has type {ty}, but the expected type is {expect}"),
    }
  }
}

impl Display for Sort {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let Sort(u) = *self;
    if u == 0 {
      write!(f, "Prop")
    } else if u == 1 {
      write!(f, "Type")
    } else {
      write!(f, "Type_{}", u - 1)
    }
  }
}

impl<'a> Display for Term<'a> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.fmt(&mut 0, &mut Vec::new(), 0, f)
  }
}

impl<'a> Term<'a> {
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

  fn fmt(
    &self,
    count: &mut usize,
    ctx: &mut Vec<usize>,
    prec: usize,
    f: &mut std::fmt::Formatter<'_>,
  ) -> std::fmt::Result {
    match *self {
      Term::Univ(u) => write!(f, "{u}"),
      Term::Var(i) => match ctx.get(ctx.len() - 1 - i) {
        Some(n) => write!(f, "{}", Self::name(*n)),
        None => write!(f, "@{}", i - ctx.len()),
      },
      Term::App(g, x) => {
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
      Term::Lam(t, x) => {
        if prec > 1 {
          write!(f, "(")?;
        }
        write!(f, "({} : ", Self::name(*count))?;
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
      Term::Pi(s, t) => {
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
      Term::Let(v, x) => {
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
