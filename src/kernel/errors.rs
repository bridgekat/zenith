use std::rc::Rc;

use super::*;

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
pub enum TypeError {
  EvalError { err: EvalError },
  UnivForm { univ: usize },
  PiForm { from: usize, to: usize },
  SigForm { fst: usize, snd: usize },
  CtxIndex { ix: usize, len: usize },
  SigInit { n: usize, len: usize },
  SigProj { n: usize, len: usize },
  AnnExpected { term: Rc<Term> },
  TypeExpected { term: Rc<Term>, ty: Rc<Term> },
  PiExpected { term: Rc<Term>, ty: Rc<Term> },
  SigExpected { term: Rc<Term>, ty: Rc<Term> },
  PiAnnExpected { ty: Rc<Term> },
  SigAnnExpected { ty: Rc<Term> },
  TypeMismatch { term: Rc<Term>, ty: Rc<Term>, ety: Rc<Term> },
  TupSizeMismatch { term: Rc<Term>, sz: usize, esz: usize },
}

/// # Lexing errors
///
/// Errors produced by the simple lexer. Positions are in numbers of characters instead of bytes.
#[derive(Debug, Clone)]
pub enum LexError {
  UnexpectedChar { ch: char, pos: usize },
  UnexpectedEof,
}

/// # Parsing errors
///
/// Errors produced by the simple parser. Positions are in numbers of characters instead of bytes.
#[derive(Debug, Clone)]
pub enum ParseError {
  Lex { err: LexError },
  UndefinedIdent { name: String, start: usize, end: usize },
  UnexpectedToken { tok: Token, start: usize, end: usize },
  UnexpectedEof,
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
}

impl TypeError {
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

  pub fn ann_expected(term: Rc<Term>) -> Self {
    Self::AnnExpected { term }
  }

  pub fn type_expected(term: Rc<Term>, ty: Val, ctx: &Stack, _env: &Stack) -> Self {
    match ty.quote(ctx.len()) {
      Ok(ty) => Self::TypeExpected { term, ty: Rc::new(ty) },
      Err(err) => err.into(),
    }
  }

  pub fn pi_expected(term: Rc<Term>, ty: Val, ctx: &Stack, _env: &Stack) -> Self {
    match ty.quote(ctx.len()) {
      Ok(ty) => Self::PiExpected { term, ty: Rc::new(ty) },
      Err(err) => err.into(),
    }
  }

  pub fn sig_expected(term: Rc<Term>, ty: Val, ctx: &Stack, _env: &Stack) -> Self {
    match ty.quote(ctx.len()) {
      Ok(ty) => Self::SigExpected { term, ty: Rc::new(ty) },
      Err(err) => err.into(),
    }
  }

  pub fn pi_ann_expected(ty: Val, ctx: &Stack, _env: &Stack) -> Self {
    match ty.quote(ctx.len()) {
      Ok(ty) => Self::PiAnnExpected { ty: Rc::new(ty) },
      Err(err) => err.into(),
    }
  }

  pub fn sig_ann_expected(ty: Val, ctx: &Stack, _env: &Stack) -> Self {
    match ty.quote(ctx.len()) {
      Ok(ty) => Self::SigAnnExpected { ty: Rc::new(ty) },
      Err(err) => err.into(),
    }
  }

  pub fn type_mismatch(term: Rc<Term>, ty: Val, ety: Val, ctx: &Stack, _env: &Stack) -> Self {
    match ty.quote(ctx.len()) {
      Ok(ty) => match ety.quote(ctx.len()) {
        Ok(ety) => Self::TypeMismatch { term, ty: Rc::new(ty), ety: Rc::new(ety) },
        Err(err) => err.into(),
      },
      Err(err) => err.into(),
    }
  }

  pub fn tup_size_mismatch(term: Rc<Term>, sz: usize, esz: usize) -> Self {
    Self::TupSizeMismatch { term, sz, esz }
  }
}

impl std::convert::From<EvalError> for TypeError {
  fn from(err: EvalError) -> Self {
    Self::EvalError { err }
  }
}

impl LexError {
  pub fn unexpected(next: Option<(usize, char)>) -> Self {
    match next {
      Some((pos, ch)) => Self::UnexpectedChar { ch, pos },
      None => Self::UnexpectedEof,
    }
  }

  pub fn position(&self, chars: usize) -> (usize, usize) {
    match self {
      Self::UnexpectedChar { ch: _, pos } => (*pos, *pos),
      Self::UnexpectedEof => (chars, chars),
    }
  }
}

impl ParseError {
  pub fn undefined_id(name: String, start: usize, end: usize) -> Self {
    Self::UndefinedIdent { name, start, end }
  }

  pub fn unexpected(next: Option<Span>) -> Self {
    match next {
      Some(span) => Self::UnexpectedToken { tok: span.tok, start: span.start, end: span.end },
      None => Self::UnexpectedEof,
    }
  }

  pub fn position(&self, chars: usize) -> (usize, usize) {
    match self {
      Self::Lex { err } => err.position(chars),
      Self::UndefinedIdent { start, end, .. } => (*start, *end),
      Self::UnexpectedToken { start, end, .. } => (*start, *end),
      Self::UnexpectedEof => (chars, chars),
    }
  }
}

impl std::convert::From<LexError> for ParseError {
  fn from(err: LexError) -> Self {
    Self::Lex { err }
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

impl std::fmt::Display for TypeError {
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
    }
  }
}

impl std::fmt::Display for LexError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::UnexpectedChar { ch, pos: _ } => write!(f, "unexpected character {ch}"),
      Self::UnexpectedEof => write!(f, "unexpected end of input"),
    }
  }
}

impl std::fmt::Display for ParseError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Lex { err } => write!(f, "{err}"),
      Self::UndefinedIdent { name, start: _, end: _ } => write!(f, "undefined identifier {name}"),
      Self::UnexpectedToken { tok, start: _, end: _ } => write!(f, "unexpected token {tok:?}"),
      Self::UnexpectedEof => write!(f, "unexpected end of input"),
    }
  }
}
