use super::*;

use self::EvalError::*;
use self::TypeError::*;

/// # Evaluation errors
///
/// Errors produced by the evaluator (i.e. the conversion checking process).
#[derive(Debug, Clone)]
pub enum EvalError {
  EnvIndex { ix: usize, len: usize },
  GenLevel { lvl: usize, len: usize },
}

impl EvalError {
  pub fn env_index(ix: usize, len: usize) -> Self {
    EnvIndex { ix, len }
  }

  pub fn gen_level(lvl: usize, len: usize) -> Self {
    GenLevel { lvl, len }
  }
}

/// # Type errors
///
/// Errors produced by the type checker (i.e. the type assignment process).
#[derive(Debug, Clone)]
pub enum TypeError<'a> {
  Eval { err: EvalError },
  UnivForm { univ: Univ },
  PiForm { from: Univ, to: Univ },
  SigForm { fst: Univ, snd: Univ },
  CtxIndex { ix: usize, len: usize },
  AnnExpected { term: &'a Term<'a> },
  TypeExpected { term: &'a Term<'a>, ty: &'a Term<'a> },
  PiExpected { term: &'a Term<'a>, ty: &'a Term<'a> },
  SigExpected { term: &'a Term<'a>, ty: &'a Term<'a> },
  PiAnnExpected { ty: &'a Term<'a> },
  SigAnnExpected { ty: &'a Term<'a> },
  TypeMismatch { term: &'a Term<'a>, ty: &'a Term<'a>, expect: &'a Term<'a> },
}

impl std::convert::From<EvalError> for TypeError<'_> {
  fn from(err: EvalError) -> Self {
    Eval { err }
  }
}

impl<'a> TypeError<'a> {
  pub fn univ_form(univ: Univ) -> Self {
    UnivForm { univ }
  }

  pub fn pi_form(from: Univ, to: Univ) -> Self {
    PiForm { from, to }
  }

  pub fn sig_form(fst: Univ, snd: Univ) -> Self {
    SigForm { fst, snd }
  }

  pub fn ctx_index(ix: usize, len: usize) -> Self {
    CtxIndex { ix, len }
  }

  pub fn ann_expected(term: &'a Term<'a>) -> Self {
    AnnExpected { term }
  }

  pub fn type_expected(term: &'a Term<'a>, ty: Val<'a>, lvl: usize, ar: &'a Arena<'a>) -> Self {
    match ty.quote(lvl, ar) {
      Ok(ty) => TypeExpected { term, ty: ar.term(ty) },
      Err(err) => Eval { err },
    }
  }

  pub fn pi_expected(term: &'a Term<'a>, ty: Val<'a>, lvl: usize, ar: &'a Arena<'a>) -> Self {
    match ty.quote(lvl, ar) {
      Ok(ty) => PiExpected { term, ty: ar.term(ty) },
      Err(err) => Eval { err },
    }
  }

  pub fn sig_expected(term: &'a Term<'a>, ty: Val<'a>, lvl: usize, ar: &'a Arena<'a>) -> Self {
    match ty.quote(lvl, ar) {
      Ok(ty) => SigExpected { term, ty: ar.term(ty) },
      Err(err) => Eval { err },
    }
  }

  pub fn pi_ann_expected(ty: Val<'a>, lvl: usize, ar: &'a Arena<'a>) -> Self {
    match ty.quote(lvl, ar) {
      Ok(ty) => PiAnnExpected { ty: ar.term(ty) },
      Err(err) => Eval { err },
    }
  }

  pub fn sig_ann_expected(ty: Val<'a>, lvl: usize, ar: &'a Arena<'a>) -> Self {
    match ty.quote(lvl, ar) {
      Ok(ty) => SigAnnExpected { ty: ar.term(ty) },
      Err(err) => Eval { err },
    }
  }

  pub fn type_mismatch(term: &'a Term<'a>, ty: Val<'a>, expect: Val<'a>, lvl: usize, ar: &'a Arena<'a>) -> Self {
    match ty.quote(lvl, ar) {
      Ok(ty) => match expect.quote(lvl, ar) {
        Ok(expect) => TypeMismatch { term, ty: ar.term(ty), expect: ar.term(expect) },
        Err(err) => Eval { err },
      },
      Err(err) => Eval { err },
    }
  }
}

impl std::fmt::Display for EvalError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      EnvIndex { ix, len } => write!(f, "variable index {ix} out of bound, environment has size {len}"),
      GenLevel { lvl, len } => write!(f, "generic variable level {lvl} out of bound, environment has size {len}"),
    }
  }
}

impl std::fmt::Display for TypeError<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Eval { err } => write!(f, "{err}"),
      UnivForm { univ } => write!(f, "universe {univ} does not have a type"),
      PiForm { from, to } => write!(f, "dependent functions from {from} to {to} are unspecified"),
      SigForm { fst, snd } => write!(f, "dependent pairs with {fst} and {snd} are unspecified"),
      CtxIndex { ix, len } => write!(f, "variable index {ix} out of bound, context has size {len}"),
      AnnExpected { term } => write!(f, "type annotation expected around term {term}"),
      TypeExpected { term, ty } => write!(f, "type expected, term {term} has type {ty} but not universe type"),
      PiExpected { term, ty } => write!(f, "function expected, term {term} has type {ty} but not function type"),
      SigExpected { term, ty } => write!(f, "pair expected, term {term} has type {ty} but not pair type"),
      PiAnnExpected { ty } => write!(f, "function found but type annotation {ty} is not function type"),
      SigAnnExpected { ty } => write!(f, "pair found but type annotation {ty} is not pair type"),
      TypeMismatch { term, ty, expect } => write!(f, "term {term} has type {ty}, but the expected type is {expect}"),
    }
  }
}

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

impl std::fmt::Display for Term<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.fmt(&mut 0, &mut Vec::new(), f)
  }
}

impl Term<'_> {
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
      Term::Var(ix) => match *ix < names.len() {
        true => write!(f, "{}", Self::name(names[names.len() - 1 - ix])),
        false => write!(f, "^{}", ix - names.len()),
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
