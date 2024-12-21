use super::*;

/// # Evaluation errors
///
/// Errors produced by the evaluator (i.e. the conversion checking process).
#[derive(Debug, Clone)]
pub enum EvalError {
  EnvIndex { ix: usize, len: usize },
  GenLevel { lvl: usize, len: usize },
}

/// # Typing errors
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
  TypeMismatch { term: &'a Term<'a>, ty: &'a Term<'a>, ety: &'a Term<'a> },
}

/// # Lexing errors
///
/// Errors produced by the simple lexer.
#[derive(Debug, Clone)]
pub enum LexError {
  UnexpectedChar { ch: char, pos: usize },
  UnexpectedEof,
}

/// # Parsing errors
///
/// Errors produced by the simple parser.
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
}

impl<'a> TypeError<'a> {
  pub fn univ_form(univ: Univ) -> Self {
    Self::UnivForm { univ }
  }

  pub fn pi_form(from: Univ, to: Univ) -> Self {
    Self::PiForm { from, to }
  }

  pub fn sig_form(fst: Univ, snd: Univ) -> Self {
    Self::SigForm { fst, snd }
  }

  pub fn ctx_index(ix: usize, len: usize) -> Self {
    Self::CtxIndex { ix, len }
  }

  pub fn ann_expected(term: &'a Term<'a>) -> Self {
    Self::AnnExpected { term }
  }

  pub fn type_expected(term: &'a Term<'a>, ty: Val<'a>, lvl: usize, ar: &'a Arena<'a>) -> Self {
    match ty.quote(lvl, ar) {
      Ok(ty) => Self::TypeExpected { term, ty: ar.term(ty) },
      Err(err) => err.into(),
    }
  }

  pub fn pi_expected(term: &'a Term<'a>, ty: Val<'a>, lvl: usize, ar: &'a Arena<'a>) -> Self {
    match ty.quote(lvl, ar) {
      Ok(ty) => Self::PiExpected { term, ty: ar.term(ty) },
      Err(err) => err.into(),
    }
  }

  pub fn sig_expected(term: &'a Term<'a>, ty: Val<'a>, lvl: usize, ar: &'a Arena<'a>) -> Self {
    match ty.quote(lvl, ar) {
      Ok(ty) => Self::SigExpected { term, ty: ar.term(ty) },
      Err(err) => err.into(),
    }
  }

  pub fn pi_ann_expected(ty: Val<'a>, lvl: usize, ar: &'a Arena<'a>) -> Self {
    match ty.quote(lvl, ar) {
      Ok(ty) => Self::PiAnnExpected { ty: ar.term(ty) },
      Err(err) => err.into(),
    }
  }

  pub fn sig_ann_expected(ty: Val<'a>, lvl: usize, ar: &'a Arena<'a>) -> Self {
    match ty.quote(lvl, ar) {
      Ok(ty) => Self::SigAnnExpected { ty: ar.term(ty) },
      Err(err) => err.into(),
    }
  }

  pub fn type_mismatch(term: &'a Term<'a>, ty: Val<'a>, expect: Val<'a>, lvl: usize, ar: &'a Arena<'a>) -> Self {
    match ty.quote(lvl, ar) {
      Ok(ty) => match expect.quote(lvl, ar) {
        Ok(expect) => Self::TypeMismatch { term, ty: ar.term(ty), ety: ar.term(expect) },
        Err(err) => err.into(),
      },
      Err(err) => err.into(),
    }
  }
}

impl std::convert::From<EvalError> for TypeError<'_> {
  fn from(err: EvalError) -> Self {
    Self::Eval { err }
  }
}

impl LexError {
  pub fn unexpected(next: Option<(usize, char)>) -> Self {
    match next {
      Some((pos, ch)) => Self::UnexpectedChar { ch, pos },
      None => Self::UnexpectedEof,
    }
  }

  pub fn position(&self, len: usize) -> (usize, usize) {
    match self {
      Self::UnexpectedChar { ch: _, pos } => (*pos, *pos),
      Self::UnexpectedEof => (len, len),
    }
  }
}

impl ParseError {
  pub fn undefined_ident(name: String, start: usize, end: usize) -> Self {
    Self::UndefinedIdent { name, start, end }
  }

  pub fn unexpected(next: Option<Span>) -> Self {
    match next {
      Some(span) => Self::UnexpectedToken { tok: span.tok, start: span.start, end: span.end },
      None => Self::UnexpectedEof,
    }
  }

  pub fn position(&self, len: usize) -> (usize, usize) {
    match self {
      Self::Lex { err } => err.position(len),
      Self::UndefinedIdent { start, end, .. } => (*start, *end),
      Self::UnexpectedToken { start, end, .. } => (*start, *end),
      Self::UnexpectedEof => (len, len),
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
    }
  }
}

impl std::fmt::Display for TypeError<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Eval { err } => write!(f, "{err}"),
      Self::UnivForm { univ } => write!(f, "universe {univ} does not have a type"),
      Self::PiForm { from, to } => write!(f, "dependent functions from {from} to {to} are unspecified"),
      Self::SigForm { fst, snd } => write!(f, "dependent pairs with {fst} and {snd} are unspecified"),
      Self::CtxIndex { ix, len } => write!(f, "variable index {ix} out of bound, context has size {len}"),
      Self::AnnExpected { term } => write!(f, "type annotation expected around term {term}"),
      Self::TypeExpected { term, ty } => write!(f, "type expected, term {term} has type {ty} but not universe type"),
      Self::PiExpected { term, ty } => write!(f, "function expected, term {term} has type {ty} but not function type"),
      Self::SigExpected { term, ty } => write!(f, "pair expected, term {term} has type {ty} but not pair type"),
      Self::PiAnnExpected { ty } => write!(f, "function found but type annotation {ty} is not function type"),
      Self::SigAnnExpected { ty } => write!(f, "pair found but type annotation {ty} is not pair type"),
      Self::TypeMismatch { term, ty, ety } => write!(f, "term {term} has type {ty}, but the expected type is {ety}"),
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
