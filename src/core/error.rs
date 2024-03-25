use std::fmt::Display;

use self::TypeError::*;
use super::term::*;

#[derive(Debug, Clone, Copy)]
pub enum TypeError<'a> {
  UniverseOverflow { term: &'a Term<'a>, sort: Sort },
  FunctionOverflow { term: &'a Term<'a>, from: Sort, to: Sort },
  VariableOverflow { term: &'a Term<'a>, var: usize, len: usize },
  FunctionExpected { term: &'a Term<'a>, ty: &'a Term<'a> },
  TypeExpected { term: &'a Term<'a>, ty: &'a Term<'a> },
  TypeMismatch { term: &'a Term<'a>, ty: &'a Term<'a>, expect: &'a Term<'a> },
}

impl<'a> Display for TypeError<'a> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      UniverseOverflow { term: _, sort } => write!(f, "universe {sort} does not have a type"),
      FunctionOverflow { term: _, from, to } => write!(f, "dependent functions from {from} to {to} are unspecified"),
      VariableOverflow { term: _, var, len } => write!(f, "variable index {var} out of bound: current depth is {len}"),
      FunctionExpected { term, ty } => write!(f, "function expected, term {term} has type {ty}, which is not Pi type"),
      TypeExpected { term, ty } => write!(f, "type expected, term {term} has type {ty}, which is not universe type"),
      TypeMismatch { term, ty, expect } => write!(f, "term {term} has type {ty}, but the expected type is {expect}"),
    }
  }
}
