use super::*;
use crate::arena::Arena;

/// # Evaluation errors
///
/// Errors produced by the evaluator (i.e. the conversion checking process).
#[derive(Debug, Clone)]
pub enum EvalError {
  EnvIndex { ix: usize, len: usize },
  GenLevel { lvl: usize, len: usize },
  TupInit { n: usize, len: usize },
  TupProj { n: usize, len: usize },
}

/// # Typing errors
///
/// Errors produced by the typer (i.e. the bidirectional infer/check process).
#[derive(Debug, Clone)]
pub enum TypeError<'b, 'c, T: Decoration<'c>> {
  EvalError { err: EvalError },
  UnivForm { univ: usize },
  PiForm { from: usize, to: usize },
  SigForm { fst: usize, snd: usize },
  CtxIndex { ix: usize, len: usize },
  SigInit { n: usize, len: usize },
  SigProj { n: usize, len: usize },
  AnnExpected { term: &'b Term<'b, 'c, T> },
  TypeExpected { term: &'b Term<'b, 'c, T>, ty: &'b Term<'b, 'c, Core<'c>> },
  PiExpected { term: &'b Term<'b, 'c, T>, ty: &'b Term<'b, 'c, Core<'c>> },
  SigExpected { term: &'b Term<'b, 'c, T>, ty: &'b Term<'b, 'c, Core<'c>> },
  PiAnnExpected { ty: &'b Term<'b, 'c, Core<'c>> },
  SigAnnExpected { ty: &'b Term<'b, 'c, Core<'c>> },
  TypeMismatch { term: &'b Term<'b, 'c, T>, ty: &'b Term<'b, 'c, Core<'c>>, ety: &'b Term<'b, 'c, Core<'c>> },
  TupSizeMismatch { term: &'b Term<'b, 'c, T>, sz: usize, esz: usize },
  TupFieldMismatch { term: &'b Term<'b, 'c, T>, name: &'c str, ename: &'c str },
}

impl EvalError {
  pub fn env_index(ix: usize, len: usize) -> Self {
    Self::EnvIndex { ix, len }
  }

  pub fn gen_level(lvl: usize, len: usize) -> Self {
    Self::GenLevel { lvl, len }
  }

  pub fn tup_init(n: usize, len: usize) -> Self {
    Self::TupInit { n, len }
  }

  pub fn tup_proj(n: usize, len: usize) -> Self {
    Self::TupProj { n, len }
  }

  /// Clones `self` to given arena.
  pub fn relocate(self, _: &Arena) -> EvalError {
    match self {
      Self::EnvIndex { ix, len } => EvalError::EnvIndex { ix, len },
      Self::GenLevel { lvl, len } => EvalError::GenLevel { lvl, len },
      Self::TupInit { n, len } => EvalError::TupInit { n, len },
      Self::TupProj { n, len } => EvalError::TupProj { n, len },
    }
  }
}

impl<'b, 'c, T: Decoration<'c>> TypeError<'b, 'c, T> {
  pub fn univ_form(univ: usize) -> Self {
    Self::UnivForm { univ }
  }

  pub fn pi_form(from: usize, to: usize) -> Self {
    Self::PiForm { from, to }
  }

  pub fn sig_form(fst: usize, snd: usize) -> Self {
    Self::SigForm { fst, snd }
  }

  pub fn ctx_index(ix: usize, len: usize) -> Self {
    Self::CtxIndex { ix, len }
  }

  pub fn sig_init(n: usize, len: usize) -> Self {
    Self::SigInit { n, len }
  }

  pub fn sig_proj(n: usize, len: usize) -> Self {
    Self::SigProj { n, len }
  }

  pub fn ann_expected(term: &'b Term<'b, 'c, T>) -> Self {
    Self::AnnExpected { term }
  }

  pub fn type_expected(
    term: &'b Term<'b, 'c, T>,
    ty: Val<'b, 'c>,
    ctx: &Stack<'b, 'c>,
    _env: &Stack<'b, 'c>,
    ar: &'b Arena,
  ) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => Self::TypeExpected { term, ty },
      Err(err) => err.into(),
    }
  }

  pub fn pi_expected(
    term: &'b Term<'b, 'c, T>,
    ty: Val<'b, 'c>,
    ctx: &Stack<'b, 'c>,
    _env: &Stack<'b, 'c>,
    ar: &'b Arena,
  ) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => Self::PiExpected { term, ty },
      Err(err) => err.into(),
    }
  }

  pub fn sig_expected(
    term: &'b Term<'b, 'c, T>,
    ty: Val<'b, 'c>,
    ctx: &Stack<'b, 'c>,
    _env: &Stack<'b, 'c>,
    ar: &'b Arena,
  ) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => Self::SigExpected { term, ty },
      Err(err) => err.into(),
    }
  }

  pub fn pi_ann_expected(ty: Val<'b, 'c>, ctx: &Stack<'b, 'c>, _env: &Stack<'b, 'c>, ar: &'b Arena) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => Self::PiAnnExpected { ty },
      Err(err) => err.into(),
    }
  }

  pub fn sig_ann_expected(ty: Val<'b, 'c>, ctx: &Stack<'b, 'c>, _env: &Stack<'b, 'c>, ar: &'b Arena) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => Self::SigAnnExpected { ty },
      Err(err) => err.into(),
    }
  }

  pub fn type_mismatch(
    term: &'b Term<'b, 'c, T>,
    ty: Val<'b, 'c>,
    ety: Val<'b, 'c>,
    ctx: &Stack<'b, 'c>,
    _env: &Stack<'b, 'c>,
    ar: &'b Arena,
  ) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => match ar.val(ety).quote(ctx.len(), ar) {
        Ok(ety) => Self::TypeMismatch { term, ty, ety },
        Err(err) => err.into(),
      },
      Err(err) => err.into(),
    }
  }

  pub fn tup_size_mismatch(term: &'b Term<'b, 'c, T>, sz: usize, esz: usize) -> Self {
    Self::TupSizeMismatch { term, sz, esz }
  }

  pub fn tup_field_mismatch(term: &'b Term<'b, 'c, T>, name: &'c str, ename: &'c str) -> Self {
    Self::TupFieldMismatch { term, name, ename }
  }

  /// Clones `self` to given arena.
  pub fn relocate(self, ar: &Arena) -> TypeError<'_, 'c, T> {
    match self {
      Self::EvalError { err } => TypeError::EvalError { err: err.relocate(ar) },
      Self::UnivForm { univ } => TypeError::UnivForm { univ },
      Self::PiForm { from, to } => TypeError::PiForm { from, to },
      Self::SigForm { fst, snd } => TypeError::SigForm { fst, snd },
      Self::CtxIndex { ix, len } => TypeError::CtxIndex { ix, len },
      Self::SigInit { n, len } => TypeError::SigInit { n, len },
      Self::SigProj { n, len } => TypeError::SigProj { n, len },
      Self::AnnExpected { term } => TypeError::AnnExpected { term: term.relocate(ar) },
      Self::TypeExpected { term, ty } => TypeError::TypeExpected { term: term.relocate(ar), ty: ty.relocate(ar) },
      Self::PiExpected { term, ty } => TypeError::PiExpected { term: term.relocate(ar), ty: ty.relocate(ar) },
      Self::SigExpected { term, ty } => TypeError::SigExpected { term: term.relocate(ar), ty: ty.relocate(ar) },
      Self::PiAnnExpected { ty } => TypeError::PiAnnExpected { ty: ty.relocate(ar) },
      Self::SigAnnExpected { ty } => TypeError::SigAnnExpected { ty: ty.relocate(ar) },
      Self::TypeMismatch { term, ty, ety } => {
        TypeError::TypeMismatch { term: term.relocate(ar), ty: ty.relocate(ar), ety: ety.relocate(ar) }
      }
      Self::TupSizeMismatch { term, sz, esz } => TypeError::TupSizeMismatch { term: term.relocate(ar), sz, esz },
      Self::TupFieldMismatch { term, name, ename } => {
        TypeError::TupFieldMismatch { term: term.relocate(ar), name, ename }
      }
    }
  }
}

impl<'c, T: Decoration<'c>> std::convert::From<EvalError> for TypeError<'_, 'c, T> {
  fn from(err: EvalError) -> Self {
    Self::EvalError { err }
  }
}

impl std::fmt::Display for EvalError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::EnvIndex { ix, len } => write!(f, "variable index {ix} out of bound, environment has size {len}"),
      Self::GenLevel { lvl, len } => write!(f, "generic variable level {lvl} out of bound, environment has size {len}"),
      Self::TupInit { n, len } => write!(f, "obtaining initial segment of length {n}, tuple has size {len}"),
      Self::TupProj { n, len } => write!(f, "tuple index {n} out of bound, tuple has size {len}"),
    }
  }
}

impl<'c, T: Decoration<'c>> std::fmt::Display for TypeError<'_, 'c, T>
where
  T::Var: std::fmt::Display,
{
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::EvalError { err } => write!(f, "{err}"),
      Self::UnivForm { univ } => write!(f, "universe {univ} does not have a type"),
      Self::PiForm { from, to } => write!(f, "dependent functions from universe {from} to {to} are unspecified"),
      Self::SigForm { fst, snd } => write!(f, "dependent tuples in universes {fst} and {snd} are unspecified"),
      Self::CtxIndex { ix, len } => write!(f, "variable index {ix} out of bound, context has size {len}"),
      Self::SigInit { n, len } => write!(f, "obtaining initial segment of length {n}, tuple type has size {len}"),
      Self::SigProj { n, len } => write!(f, "tuple index {n} out of bound, tuple type has size {len}"),
      Self::AnnExpected { term } => write!(f, "type annotation expected around term {term}"),
      Self::TypeExpected { term, ty } => write!(f, "type expected, term {term} has type {ty} but not universe type"),
      Self::PiExpected { term, ty } => write!(f, "function expected, term {term} has type {ty} but not function type"),
      Self::SigExpected { term, ty } => write!(f, "tuple expected, term {term} has type {ty} but not tuple type"),
      Self::PiAnnExpected { ty } => write!(f, "function found but type annotation {ty} is not function type"),
      Self::SigAnnExpected { ty } => write!(f, "tuple found but type annotation {ty} is not tuple type"),
      Self::TypeMismatch { term, ty, ety } => write!(f, "term {term} has type {ty}, but the expected type is {ety}"),
      Self::TupSizeMismatch { term, sz, esz } => write!(f, "term {term} has size {sz}, but the expected size is {esz}"),
      Self::TupFieldMismatch { term, name, ename } => {
        write!(f, "term {term} has field with name {name}, but the expected name is {ename}")
      }
    }
  }
}

impl std::error::Error for EvalError {}
impl<'c, T: Decoration<'c>> std::error::Error for TypeError<'_, 'c, T> where T::Var: std::fmt::Display {}
