use crate::arena::Arena;
use crate::ir::{Core, EvalError, Name, Named, Stack, Term, TypeError, Val};

/// # Elaboration errors
///
/// Errors produced by the elaborator (i.e. the bidirectional infer/check process).
#[derive(Debug, Clone)]
pub enum ElabError<'a, 'b> {
  TypeError { err: TypeError<'a, 'b, Named<'b>> },
  CtxName { name: Name<'b> },
  SigName { name: Name<'b>, ty: &'a Term<'a, 'b, Core<'b>> },
}

impl<'a, 'b> ElabError<'a, 'b> {
  pub fn ctx_name(name: Name<'b>) -> Self {
    Self::CtxName { name }
  }

  pub fn sig_name(name: Name<'b>, ty: Val<'a, 'b>, ctx: &Stack<'a, 'b>, _env: &Stack<'a, 'b>, ar: &'a Arena) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => Self::SigName { name, ty },
      Err(err) => err.into(),
    }
  }

  /// Clones `self` to given arena.
  pub fn relocate(self, ar: &Arena) -> ElabError<'_, 'b> {
    match self {
      Self::TypeError { err } => ElabError::TypeError { err: err.relocate(ar) },
      Self::CtxName { name } => ElabError::CtxName { name },
      Self::SigName { name, ty } => ElabError::SigName { name, ty: ty.relocate(ar) },
    }
  }
}

impl std::convert::From<EvalError> for ElabError<'_, '_> {
  fn from(err: EvalError) -> Self {
    Self::TypeError { err: err.into() }
  }
}

impl<'a, 'b> std::convert::From<TypeError<'a, 'b, Named<'b>>> for ElabError<'a, 'b> {
  fn from(err: TypeError<'a, 'b, Named<'b>>) -> Self {
    Self::TypeError { err }
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
