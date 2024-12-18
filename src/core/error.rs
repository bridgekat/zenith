//! # Basic error handling

use self::EvalError::*;
use self::TypeError::*;
use super::*;

#[derive(Debug, Clone)]
pub enum EvalError {
  EnvIndex { ix: usize, len: usize },
}

#[derive(Debug, Clone)]
pub enum TypeError<'a> {
  Eval { err: EvalError },
  UnivForm { univ: Univ },
  PiForm { from: Univ, to: Univ },
  SigForm { fst: Univ, snd: Univ },
  CtxIndex { ix: usize, len: usize },
  AnnExpected { term: &'a Term<'a> },
  TypeExpected { term: &'a Term<'a>, ty: Val<'a> },
  PiExpected { term: &'a Term<'a>, ty: Val<'a> },
  SigExpected { term: &'a Term<'a>, ty: Val<'a> },
  PiAnnExpected { ty: Val<'a> },
  SigAnnExpected { ty: Val<'a> },
  TypeMismatch { term: &'a Term<'a>, ty: Val<'a>, expect: Val<'a> },
}

impl<'a> std::convert::From<EvalError> for TypeError<'a> {
  fn from(err: EvalError) -> Self {
    Eval { err }
  }
}

/// Simple pretty-printer for debugging purposes.
impl std::fmt::Display for EvalError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      EnvIndex { ix, len } => write!(f, "variable index {ix} out of bound, environment has size {len}"),
    }
  }
}

/// Simple pretty-printer for debugging purposes.
impl<'a> std::fmt::Display for TypeError<'a> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Eval { err } => write!(f, "{err}"),
      UnivForm { univ } => write!(f, "universe {univ} does not have a type"),
      PiForm { from, to } => write!(f, "dependent functions from {from} to {to} are unspecified"),
      SigForm { fst, snd } => write!(f, "dependent pairs with {fst} and {snd} are unspecified"),
      CtxIndex { ix, len } => write!(f, "variable index {ix} out of bound, context has size {len}"),
      AnnExpected { term } => write!(f, "type annotation expected around term {term}"),
      TypeExpected { term, ty: _ } => write!(f, "type expected, term {term} has type ? but not universe type"),
      PiExpected { term, ty: _ } => write!(f, "function expected, term {term} has type ? but not function type"),
      SigExpected { term, ty: _ } => write!(f, "pair expected, term {term} has type ? but not pair type"),
      PiAnnExpected { ty: _ } => write!(f, "function found but type annotation ? is not function type"),
      SigAnnExpected { ty: _ } => write!(f, "pair found but type annotation ? is not pair type"),
      TypeMismatch { term, ty: _, expect: _ } => write!(f, "term {term} has type ?, but the expected type is ?"),
    }
  }
}

/// Simple pretty-printer for debugging purposes.
impl std::fmt::Display for Univ {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let Univ(u) = *self;
    if u == 0 {
      write!(f, "TYPE")
    } else {
      write!(f, "KIND")
    }
  }
}

/// Simple pretty-printer for debugging purposes.
impl<'a> std::fmt::Display for Term<'a> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.fmt(&mut 0, &mut Vec::new(), f)
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

  fn fmt(&self, count: &mut usize, names: &mut Vec<usize>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Term::Univ(univ) => write!(f, "{univ}"),
      Term::Var(ix) => match names.get(names.len() - 1 - ix) {
        Some(n) => write!(f, "{}", Self::name(*n)),
        None => write!(f, "@{}", ix - names.len()),
      },
      Term::Ann(x, t) => {
        write!(f, "(")?;
        x.fmt(count, names, f)?;
        write!(f, ") : (")?;
        t.fmt(count, names, f)?;
        write!(f, ")")?;
        Ok(())
      }
      Term::Let(v, x) => {
        write!(f, "[{} := ", Self::name(*count))?;
        v.fmt(count, names, f)?;
        write!(f, "] ")?;
        names.push(*count);
        *count += 1;
        x.fmt(count, names, f)?;
        names.pop();
        Ok(())
      }
      Term::Pi(s, t) => {
        write!(f, "[{} : ", Self::name(*count))?;
        s.fmt(count, names, f)?;
        write!(f, "] -> ")?;
        names.push(*count);
        *count += 1;
        t.fmt(count, names, f)?;
        names.pop();
        Ok(())
      }
      Term::Fun(b) => {
        write!(f, "[{}] => ", Self::name(*count))?;
        names.push(*count);
        *count += 1;
        b.fmt(count, names, f)?;
        names.pop();
        Ok(())
      }
      Term::App(g, x) => {
        write!(f, "(")?;
        g.fmt(count, names, f)?;
        write!(f, ") (")?;
        x.fmt(count, names, f)?;
        write!(f, ")")?;
        Ok(())
      }
      Term::Sig(s, t) => {
        write!(f, "[{} : ", Self::name(*count))?;
        s.fmt(count, names, f)?;
        write!(f, "] ;; ")?;
        names.push(*count);
        *count += 1;
        t.fmt(count, names, f)?;
        names.pop();
        Ok(())
      }
      Term::Pair(a, b) => {
        write!(f, "[{} := ", Self::name(*count))?;
        a.fmt(count, names, f)?;
        write!(f, "] ; ")?;
        names.push(*count);
        *count += 1;
        b.fmt(count, names, f)?;
        names.pop();
        Ok(())
      }
      Term::Fst(x) => {
        write!(f, "(")?;
        x.fmt(count, names, f)?;
        write!(f, ") <")?;
        Ok(())
      }
      Term::Snd(x) => {
        write!(f, "(")?;
        x.fmt(count, names, f)?;
        write!(f, ") >")?;
        Ok(())
      }
      Term::Unit => write!(f, "[]"),
      Term::Star => write!(f, "[]"),
    }
  }
}
