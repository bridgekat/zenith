use crate::arena::{Arena, Relocate};
use crate::ir::{Core, EvalError, Named, Stack, Term, TypeError, Val};

/// # Elaboration errors
///
/// Errors produced by the elaborator (i.e. the bidirectional infer/check process).
#[derive(Debug, Clone)]
pub enum ElabError<'a, 'b> {
  TypeError { err: TypeError<'a, 'b, Named> },
  CtxName { name: &'b str },
  SigName { name: &'b str, ty: &'a Term<'a, 'b, Core> },
}

impl<'a, 'b> ElabError<'a, 'b> {
  pub fn ctx_name(name: &'b str) -> Self {
    Self::CtxName { name }
  }

  pub fn sig_name(name: &'b str, ty: Val<'a, 'b>, ctx: &Stack<'a, 'b>, _env: &Stack<'a, 'b>, ar: &'a Arena) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => Self::SigName { name, ty: ar.term(ty) },
      Err(err) => err.into(),
    }
  }
}

impl<'a, 'b> std::convert::From<EvalError<'a, 'b>> for ElabError<'a, 'b> {
  fn from(err: EvalError<'a, 'b>) -> Self {
    Self::TypeError { err: err.into() }
  }
}

impl<'a, 'b> std::convert::From<TypeError<'a, 'b, Named>> for ElabError<'a, 'b> {
  fn from(err: TypeError<'a, 'b, Named>) -> Self {
    Self::TypeError { err }
  }
}

impl<'a, 'b> Relocate<'a, ElabError<'a, 'b>> for ElabError<'_, 'b> {
  fn relocate(&self, ar: &'a Arena) -> ElabError<'a, 'b> {
    match self {
      Self::TypeError { err } => ElabError::TypeError { err: err.relocate(ar) },
      Self::CtxName { name } => ElabError::CtxName { name },
      Self::SigName { name, ty } => ElabError::SigName { name, ty: ar.term(ty.relocate(ar)) },
    }
  }
}

impl std::fmt::Display for ElabError<'_, '_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::TypeError { err } => write!(f, "{err}"),
      Self::CtxName { name } => write!(f, "unresolved variable name {name}"),
      Self::SigName { name, ty } => write!(f, "field {name} not found in tuple type {ty}"),
    }
  }
}

impl std::error::Error for ElabError<'_, '_> {}
