use super::*;
use crate::arena::Arena;

/// # Evaluation errors
///
/// Errors produced by the evaluator (i.e. the conversion checking process).
#[derive(Debug, Clone)]
pub enum EvalError<'a> {
  EnvIndex { ix: usize, len: usize },
  GenLevel { lvl: usize, len: usize },
  TupInit { n: usize, len: usize },
  TupLast { n: usize, len: usize },
  SigImproper { head: &'a Term<'a> },
  TupImproper { head: &'a Term<'a> },
}

impl<'a> EvalError<'a> {
  pub fn env_index(ix: usize, len: usize) -> Self {
    Self::EnvIndex { ix, len }
  }

  pub fn gen_level(lvl: usize, len: usize) -> Self {
    Self::GenLevel { lvl, len }
  }

  pub fn tup_init(n: usize, len: usize) -> Self {
    Self::TupInit { n, len }
  }

  pub fn tup_last(n: usize, len: usize) -> Self {
    Self::TupLast { n, len }
  }

  pub fn sig_improper(head: &'a Term<'a>) -> Self {
    Self::SigImproper { head }
  }

  pub fn tup_improper(head: &'a Term<'a>) -> Self {
    Self::TupImproper { head }
  }

  /// Clones `self` to given arena.
  pub fn relocate(self, ar: &Arena) -> EvalError {
    match self {
      Self::EnvIndex { ix, len } => EvalError::EnvIndex { ix, len },
      Self::GenLevel { lvl, len } => EvalError::GenLevel { lvl, len },
      Self::TupInit { n, len } => EvalError::TupInit { n, len },
      Self::TupLast { n, len } => EvalError::TupLast { n, len },
      Self::SigImproper { head } => EvalError::SigImproper { head: head.relocate(ar) },
      Self::TupImproper { head } => EvalError::TupImproper { head: head.relocate(ar) },
    }
  }
}

impl std::fmt::Display for EvalError<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::EnvIndex { ix, len } => write!(f, "variable index {ix} out of bound, environment has size {len}"),
      Self::GenLevel { lvl, len } => write!(f, "generic variable level {lvl} out of bound, environment has size {len}"),
      Self::TupInit { n, len } => write!(f, "obtaining initial segment of length {n}, tuple has size {len}"),
      Self::TupLast { n: _, len: _ } => write!(f, "obtaining last element of empty tuple"),
      Self::SigImproper { head: _ } => write!(f, "dependent tuple type must begin with unit"),
      Self::TupImproper { head: _ } => write!(f, "dependent tuple value must begin with unit"),
    }
  }
}

impl std::error::Error for EvalError<'_> {}
