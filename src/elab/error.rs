use std::fmt::Display;

use super::*;

#[derive(Debug, Clone, Copy)]
pub enum Error<'a> {
  UnresolvedMeta { term: &'a Term<'a> },
}

impl<'a> Display for Error<'a> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Error::UnresolvedMeta { term: _ } => write!(f, "unexpected metavariable..."),
    }
  }
}
