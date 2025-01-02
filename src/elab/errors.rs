use super::*;
use crate::arena::Arena;
use crate::ir;

/// # Typing errors
///
/// Errors produced by the typer (i.e. the bidirectional infer/check process).
#[derive(Debug, Clone)]
pub enum TypeError<'a> {
  Eval { err: ir::EvalError<'a> },
  UnivForm { univ: usize },
  PiForm { from: usize, to: usize },
  SigForm { fst: usize, snd: usize },
  CtxIndex { ix: usize, len: usize },
  CtxName { name: Name<'a> },
  SigInit { n: usize, len: usize },
  SigLast { n: usize, len: usize },
  SigName { name: Name<'a>, ty: &'a Term<'a> },
  SigImproper { head: &'a Term<'a> },
  TupImproper { head: &'a Term<'a> },
  AnnExpected { term: &'a Term<'a> },
  TypeExpected { term: &'a Term<'a>, ty: &'a Term<'a> },
  PiExpected { term: &'a Term<'a>, ty: &'a Term<'a> },
  SigExpected { term: &'a Term<'a>, ty: &'a Term<'a> },
  PiAnnExpected { ty: &'a Term<'a> },
  SigAnnExpected { ty: &'a Term<'a> },
  TypeMismatch { term: &'a Term<'a>, ty: &'a Term<'a>, ety: &'a Term<'a> },
  TupSizeMismatch { term: &'a Term<'a>, sz: usize, esz: usize },
  TupFieldMismatch { term: &'a Term<'a>, name: &'a str, ename: &'a str },
}

impl<'a> TypeError<'a> {
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

  pub fn ctx_name(name: Name<'a>) -> Self {
    Self::CtxName { name }
  }

  pub fn sig_init(n: usize, len: usize) -> Self {
    Self::SigInit { n, len }
  }

  pub fn sig_last(n: usize, len: usize) -> Self {
    Self::SigLast { n, len }
  }

  pub fn sig_name<'b>(
    name: Name<'a>,
    ty: ir::Val<'b, 'a>,
    ctx: &ir::Stack<'b, 'a>,
    _env: &ir::Stack<'b, 'a>,
    ar: &'a Arena,
  ) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => Self::SigName { name, ty },
      Err(err) => err.into(),
    }
  }

  pub fn sig_improper(head: &'a Term<'a>) -> Self {
    Self::SigImproper { head }
  }

  pub fn tup_improper(head: &'a Term<'a>) -> Self {
    Self::TupImproper { head }
  }

  pub fn ann_expected(term: &'a Term<'a>) -> Self {
    Self::AnnExpected { term }
  }

  pub fn type_expected<'b>(
    term: &'a Term<'a>,
    ty: ir::Val<'b, 'a>,
    ctx: &ir::Stack<'b, 'a>,
    _env: &ir::Stack<'b, 'a>,
    ar: &'a Arena,
  ) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => Self::TypeExpected { term, ty },
      Err(err) => err.into(),
    }
  }

  pub fn pi_expected<'b>(
    term: &'a Term<'a>,
    ty: ir::Val<'b, 'a>,
    ctx: &ir::Stack<'b, 'a>,
    _env: &ir::Stack<'b, 'a>,
    ar: &'a Arena,
  ) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => Self::PiExpected { term, ty },
      Err(err) => err.into(),
    }
  }

  pub fn sig_expected<'b>(
    term: &'a Term<'a>,
    ty: ir::Val<'b, 'a>,
    ctx: &ir::Stack<'b, 'a>,
    _env: &ir::Stack<'b, 'a>,
    ar: &'a Arena,
  ) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => Self::SigExpected { term, ty },
      Err(err) => err.into(),
    }
  }

  pub fn pi_ann_expected<'b>(
    ty: ir::Val<'b, 'a>,
    ctx: &ir::Stack<'b, 'a>,
    _env: &ir::Stack<'b, 'a>,
    ar: &'a Arena,
  ) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => Self::PiAnnExpected { ty },
      Err(err) => err.into(),
    }
  }

  pub fn sig_ann_expected<'b>(
    ty: ir::Val<'b, 'a>,
    ctx: &ir::Stack<'b, 'a>,
    _env: &ir::Stack<'b, 'a>,
    ar: &'a Arena,
  ) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => Self::SigAnnExpected { ty },
      Err(err) => err.into(),
    }
  }

  pub fn type_mismatch<'b>(
    term: &'a Term<'a>,
    ty: ir::Val<'b, 'a>,
    expect: ir::Val<'b, 'a>,
    ctx: &ir::Stack<'b, 'a>,
    _env: &ir::Stack<'b, 'a>,
    ar: &'a Arena,
  ) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => match ar.val(expect).quote(ctx.len(), ar) {
        Ok(ety) => Self::TypeMismatch { term, ty, ety },
        Err(err) => err.into(),
      },
      Err(err) => err.into(),
    }
  }

  pub fn tup_size_mismatch(term: &'a Term<'a>, sz: usize, esz: usize) -> Self {
    Self::TupSizeMismatch { term, sz, esz }
  }

  pub fn tup_field_mismatch(term: &'a Term<'a>, name: &'a str, ename: &'a str) -> Self {
    Self::TupFieldMismatch { term, name, ename }
  }

  /// Clones `self` to given arena.
  pub fn relocate(self, ar: &Arena) -> TypeError {
    match self {
      Self::Eval { err } => TypeError::Eval { err: err.relocate(ar) },
      Self::UnivForm { univ } => TypeError::UnivForm { univ },
      Self::PiForm { from, to } => TypeError::PiForm { from, to },
      Self::SigForm { fst, snd } => TypeError::SigForm { fst, snd },
      Self::CtxIndex { ix, len } => TypeError::CtxIndex { ix, len },
      Self::CtxName { name } => TypeError::CtxName { name: name.relocate(ar) },
      Self::SigInit { n, len } => TypeError::SigInit { n, len },
      Self::SigLast { n, len } => TypeError::SigLast { n, len },
      Self::SigName { name, ty } => TypeError::SigName { name: name.relocate(ar), ty: ty.relocate(ar) },
      Self::SigImproper { head } => TypeError::SigImproper { head: head.relocate(ar) },
      Self::TupImproper { head } => TypeError::TupImproper { head: head.relocate(ar) },
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
        TypeError::TupFieldMismatch { term: term.relocate(ar), name: ar.string(name), ename: ar.string(ename) }
      }
    }
  }
}

impl<'a> std::convert::From<ir::EvalError<'a>> for TypeError<'a> {
  fn from(err: ir::EvalError<'a>) -> Self {
    Self::Eval { err }
  }
}

impl std::fmt::Display for TypeError<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Eval { err } => write!(f, "{err}"),
      Self::UnivForm { univ } => write!(f, "universe {univ} does not have a type"),
      Self::PiForm { from, to } => write!(f, "dependent functions from universe {from} to {to} are unspecified"),
      Self::SigForm { fst, snd } => write!(f, "dependent tuples in universes {fst} and {snd} are unspecified"),
      Self::CtxIndex { ix, len } => write!(f, "variable index {ix} out of bound, context has size {len}"),
      Self::CtxName { name } => write!(f, "unresolved variable name {}", name.segments.join("::")),
      Self::SigImproper { head } => write!(f, "dependent tuple type must begin with unit, found {head}"),
      Self::TupImproper { head } => write!(f, "dependent tuple value must begin with unit, found {head}"),
      Self::SigInit { n, len } => write!(f, "obtaining initial segment of length {n}, tuple type has size {len}"),
      Self::SigLast { n: _, len: _ } => write!(f, "obtaining last element of empty tuple type"),
      Self::SigName { name, ty } => write!(f, "field {} not found in tuple type {ty}", name.segments.join("::")),
      Self::AnnExpected { term } => write!(f, "type annotation expected around term {term}"),
      Self::TypeExpected { term, ty } => write!(f, "type expected, term {term} has type {ty} but not universe type"),
      Self::PiExpected { term, ty } => write!(f, "function expected, term {term} has type {ty} but not function type"),
      Self::SigExpected { term, ty } => write!(f, "tuple expected, term {term} has type {ty} but not tuple type"),
      Self::PiAnnExpected { ty } => write!(f, "function found but type annotation {ty} is not function type"),
      Self::SigAnnExpected { ty } => write!(f, "tuple found but type annotation {ty} is not tuple type"),
      Self::TypeMismatch { term, ty, ety } => {
        write!(f, "term {term} has type {ty}, but the expected type is {ety}")
      }
      Self::TupSizeMismatch { term, sz, esz } => {
        write!(f, "term {term} has size {sz}, but the expected size is {esz}")
      }
      Self::TupFieldMismatch { term, name, ename } => {
        write!(f, "term {term} has field with name {name}, but the expected name is {ename}")
      }
    }
  }
}

impl std::error::Error for TypeError<'_> {}
