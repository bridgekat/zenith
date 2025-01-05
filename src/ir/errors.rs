use super::*;
use crate::arena::{Arena, Relocate};

/// # Evaluation errors
///
/// Errors produced by the evaluator (i.e. the conversion checking process).
#[derive(Debug, Clone)]
pub enum EvalError<'a, 'b> {
  EnvIndex { ix: usize, len: usize },
  GenLevel { lvl: usize, len: usize },
  TupInit { n: usize, val: &'a Term<'a, 'b, Core> },
  TupProj { n: usize, val: &'a Term<'a, 'b, Core> },
}

/// # Typing errors
///
/// Errors produced by the typer (i.e. the bidirectional infer/check process).
#[derive(Debug, Clone)]
pub enum TypeError<'a, 'b, T: Decoration> {
  EvalError { err: EvalError<'a, 'b> },
  UnivForm { univ: usize },
  PiForm { from: usize, to: usize },
  SigForm { fst: usize, snd: usize },
  CtxIndex { ix: usize, len: usize },
  SigInit { n: usize, ty: &'a Term<'a, 'b, Core> },
  SigProj { n: usize, ty: &'a Term<'a, 'b, Core> },
  AnnExpected { term: &'a Term<'a, 'b, T> },
  TypeExpected { term: &'a Term<'a, 'b, T>, ty: &'a Term<'a, 'b, Core> },
  PiExpected { term: &'a Term<'a, 'b, T>, ty: &'a Term<'a, 'b, Core> },
  SigExpected { term: &'a Term<'a, 'b, T>, ty: &'a Term<'a, 'b, Core> },
  PiAnnExpected { ty: &'a Term<'a, 'b, Core> },
  SigAnnExpected { ty: &'a Term<'a, 'b, Core> },
  TypeMismatch { term: &'a Term<'a, 'b, T>, ty: &'a Term<'a, 'b, Core>, ety: &'a Term<'a, 'b, Core> },
  TupSizeMismatch { term: &'a Term<'a, 'b, T>, sz: usize, esz: usize },
  TupFieldMismatch { term: &'a Term<'a, 'b, T>, name: &'b str, ename: &'b str },
}

impl<'a, 'b> EvalError<'a, 'b> {
  pub fn env_index(ix: usize, len: usize) -> Self {
    Self::EnvIndex { ix, len }
  }

  pub fn gen_level(lvl: usize, len: usize) -> Self {
    Self::GenLevel { lvl, len }
  }

  pub fn tup_init(n: usize, val: Val<'a, 'b>, env: &Stack<'a, 'b>, ar: &'a Arena) -> Self {
    match ar.val(val).quote(env.len(), ar) {
      Ok(val) => Self::TupInit { n, val: ar.term(val) },
      Err(err) => err,
    }
  }

  pub fn tup_proj(n: usize, val: Val<'a, 'b>, env: &Stack<'a, 'b>, ar: &'a Arena) -> Self {
    match ar.val(val).quote(env.len(), ar) {
      Ok(val) => Self::TupProj { n, val: ar.term(val) },
      Err(err) => err,
    }
  }
}

impl<'a, 'b, T: Decoration> TypeError<'a, 'b, T> {
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

  pub fn sig_init(n: usize, ty: Val<'a, 'b>, ctx: &Stack<'a, 'b>, _env: &Stack<'a, 'b>, ar: &'a Arena) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => Self::SigInit { n, ty: ar.term(ty) },
      Err(err) => err.into(),
    }
  }

  pub fn sig_proj(n: usize, ty: Val<'a, 'b>, ctx: &Stack<'a, 'b>, _env: &Stack<'a, 'b>, ar: &'a Arena) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => Self::SigProj { n, ty: ar.term(ty) },
      Err(err) => err.into(),
    }
  }

  pub fn ann_expected(term: &'a Term<'a, 'b, T>) -> Self {
    Self::AnnExpected { term }
  }

  pub fn type_expected(
    term: &'a Term<'a, 'b, T>,
    ty: Val<'a, 'b>,
    ctx: &Stack<'a, 'b>,
    _env: &Stack<'a, 'b>,
    ar: &'a Arena,
  ) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => Self::TypeExpected { term, ty: ar.term(ty) },
      Err(err) => err.into(),
    }
  }

  pub fn pi_expected(
    term: &'a Term<'a, 'b, T>,
    ty: Val<'a, 'b>,
    ctx: &Stack<'a, 'b>,
    _env: &Stack<'a, 'b>,
    ar: &'a Arena,
  ) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => Self::PiExpected { term, ty: ar.term(ty) },
      Err(err) => err.into(),
    }
  }

  pub fn sig_expected(
    term: &'a Term<'a, 'b, T>,
    ty: Val<'a, 'b>,
    ctx: &Stack<'a, 'b>,
    _env: &Stack<'a, 'b>,
    ar: &'a Arena,
  ) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => Self::SigExpected { term, ty: ar.term(ty) },
      Err(err) => err.into(),
    }
  }

  pub fn pi_ann_expected(ty: Val<'a, 'b>, ctx: &Stack<'a, 'b>, _env: &Stack<'a, 'b>, ar: &'a Arena) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => Self::PiAnnExpected { ty: ar.term(ty) },
      Err(err) => err.into(),
    }
  }

  pub fn sig_ann_expected(ty: Val<'a, 'b>, ctx: &Stack<'a, 'b>, _env: &Stack<'a, 'b>, ar: &'a Arena) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => Self::SigAnnExpected { ty: ar.term(ty) },
      Err(err) => err.into(),
    }
  }

  pub fn type_mismatch(
    term: &'a Term<'a, 'b, T>,
    ty: Val<'a, 'b>,
    ety: Val<'a, 'b>,
    ctx: &Stack<'a, 'b>,
    _env: &Stack<'a, 'b>,
    ar: &'a Arena,
  ) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => match ar.val(ety).quote(ctx.len(), ar) {
        Ok(ety) => Self::TypeMismatch { term, ty: ar.term(ty), ety: ar.term(ety) },
        Err(err) => err.into(),
      },
      Err(err) => err.into(),
    }
  }

  pub fn tup_size_mismatch(term: &'a Term<'a, 'b, T>, sz: usize, esz: usize) -> Self {
    Self::TupSizeMismatch { term, sz, esz }
  }

  pub fn tup_field_mismatch(term: &'a Term<'a, 'b, T>, name: &'b str, ename: &'b str) -> Self {
    Self::TupFieldMismatch { term, name, ename }
  }
}

impl<'a, 'b, T: Decoration> std::convert::From<EvalError<'a, 'b>> for TypeError<'a, 'b, T> {
  fn from(err: EvalError<'a, 'b>) -> Self {
    Self::EvalError { err }
  }
}

impl<'a, 'b> Relocate<'a, EvalError<'a, 'b>> for EvalError<'_, 'b> {
  fn relocate(&self, ar: &'a Arena) -> EvalError<'a, 'b> {
    match self {
      Self::EnvIndex { ix, len } => EvalError::EnvIndex { ix: *ix, len: *len },
      Self::GenLevel { lvl, len } => EvalError::GenLevel { lvl: *lvl, len: *len },
      Self::TupInit { n, val } => EvalError::TupInit { n: *n, val: ar.term(val.relocate(ar)) },
      Self::TupProj { n, val } => EvalError::TupProj { n: *n, val: ar.term(val.relocate(ar)) },
    }
  }
}

impl<'a, 'b, T: Decoration> Relocate<'a, TypeError<'a, 'b, T>> for TypeError<'_, 'b, T> {
  fn relocate(&self, ar: &'a Arena) -> TypeError<'a, 'b, T> {
    match self {
      Self::EvalError { err } => TypeError::EvalError { err: err.relocate(ar) },
      Self::UnivForm { univ } => TypeError::UnivForm { univ: *univ },
      Self::PiForm { from, to } => TypeError::PiForm { from: *from, to: *to },
      Self::SigForm { fst, snd } => TypeError::SigForm { fst: *fst, snd: *snd },
      Self::CtxIndex { ix, len } => TypeError::CtxIndex { ix: *ix, len: *len },
      Self::SigInit { n, ty } => TypeError::SigInit { n: *n, ty: ar.term(ty.relocate(ar)) },
      Self::SigProj { n, ty } => TypeError::SigProj { n: *n, ty: ar.term(ty.relocate(ar)) },
      Self::AnnExpected { term } => TypeError::AnnExpected { term: ar.term(term.relocate(ar)) },
      Self::TypeExpected { term, ty } => {
        TypeError::TypeExpected { term: ar.term(term.relocate(ar)), ty: ar.term(ty.relocate(ar)) }
      }
      Self::PiExpected { term, ty } => {
        TypeError::PiExpected { term: ar.term(term.relocate(ar)), ty: ar.term(ty.relocate(ar)) }
      }
      Self::SigExpected { term, ty } => {
        TypeError::SigExpected { term: ar.term(term.relocate(ar)), ty: ar.term(ty.relocate(ar)) }
      }
      Self::PiAnnExpected { ty } => TypeError::PiAnnExpected { ty: ar.term(ty.relocate(ar)) },
      Self::SigAnnExpected { ty } => TypeError::SigAnnExpected { ty: ar.term(ty.relocate(ar)) },
      Self::TypeMismatch { term, ty, ety } => TypeError::TypeMismatch {
        term: ar.term(term.relocate(ar)),
        ty: ar.term(ty.relocate(ar)),
        ety: ar.term(ety.relocate(ar)),
      },
      Self::TupSizeMismatch { term, sz, esz } => {
        TypeError::TupSizeMismatch { term: ar.term(term.relocate(ar)), sz: *sz, esz: *esz }
      }
      Self::TupFieldMismatch { term, name, ename } => {
        TypeError::TupFieldMismatch { term: ar.term(term.relocate(ar)), name, ename }
      }
    }
  }
}

impl std::fmt::Display for EvalError<'_, '_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::EnvIndex { ix, len } => write!(f, "variable index {ix} out of bound, environment has size {len}"),
      Self::GenLevel { lvl, len } => write!(f, "generic variable level {lvl} out of bound, environment has size {len}"),
      Self::TupInit { n, val } => write!(f, "tuple prefix length {n} out of bound, tuple has value {val}"),
      Self::TupProj { n, val } => write!(f, "tuple index {n} out of bound, tuple has value {val}"),
    }
  }
}

impl<T: Decoration> std::fmt::Display for TypeError<'_, '_, T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::EvalError { err } => write!(f, "{err}"),
      Self::UnivForm { univ } => write!(f, "universe {univ} does not have a type"),
      Self::PiForm { from, to } => write!(f, "dependent functions from universe {from} to {to} are unspecified"),
      Self::SigForm { fst, snd } => write!(f, "dependent tuples in universes {fst} and {snd} are unspecified"),
      Self::CtxIndex { ix, len } => write!(f, "variable index {ix} out of bound, context has size {len}"),
      Self::SigInit { n, ty } => write!(f, "tuple prefix length {n} out of bound, tuple has type {ty}"),
      Self::SigProj { n, ty } => write!(f, "tuple index {n} out of bound, tuple has type {ty}"),
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

impl std::error::Error for EvalError<'_, '_> {}
impl<T: Decoration> std::error::Error for TypeError<'_, '_, T> {}
