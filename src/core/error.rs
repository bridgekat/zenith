use super::*;

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

/// # Typing errors
///
/// Errors produced by the type checker (i.e. the type assignment process).
#[derive(Debug, Clone)]
pub enum TypeError<'a> {
  Eval { err: EvalError<'a> },
  UnivForm { univ: Univ },
  PiForm { from: Univ, to: Univ },
  SigForm { fst: Univ, snd: Univ },
  CtxIndex { ix: usize, len: usize },
  SigInit { n: usize, len: usize },
  SigLast { n: usize, len: usize },
  AnnExpected { term: &'a Term<'a> },
  TypeExpected { term: &'a Term<'a>, ty: &'a Term<'a> },
  PiExpected { term: &'a Term<'a>, ty: &'a Term<'a> },
  SigExpected { term: &'a Term<'a>, ty: &'a Term<'a> },
  PiAnnExpected { ty: &'a Term<'a> },
  SigAnnExpected { ty: &'a Term<'a> },
  TypeMismatch { term: &'a Term<'a>, ty: &'a Term<'a>, ety: &'a Term<'a> },
  TupSizeMismatch { term: &'a Term<'a>, sz: usize, esz: usize },
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

  pub fn sig_init(n: usize, len: usize) -> Self {
    Self::SigInit { n, len }
  }

  pub fn sig_last(n: usize, len: usize) -> Self {
    Self::SigLast { n, len }
  }

  pub fn ann_expected(term: &'a Term<'a>) -> Self {
    Self::AnnExpected { term }
  }

  pub fn type_expected<'b>(term: &'a Term<'a>, ty: Val<'b, 'a>, len: usize, ar: &'a Arena) -> Self {
    match Val::quote(ar.val(ty), len, ar) {
      Ok(ty) => Self::TypeExpected { term, ty: ar.term(ty) },
      Err(err) => err.into(),
    }
  }

  pub fn pi_expected<'b>(term: &'a Term<'a>, ty: Val<'b, 'a>, len: usize, ar: &'a Arena) -> Self {
    match Val::quote(ar.val(ty), len, ar) {
      Ok(ty) => Self::PiExpected { term, ty: ar.term(ty) },
      Err(err) => err.into(),
    }
  }

  pub fn sig_expected<'b>(term: &'a Term<'a>, ty: Val<'b, 'a>, len: usize, ar: &'a Arena) -> Self {
    match Val::quote(ar.val(ty), len, ar) {
      Ok(ty) => Self::SigExpected { term, ty: ar.term(ty) },
      Err(err) => err.into(),
    }
  }

  pub fn pi_ann_expected<'b>(ty: Val<'b, 'a>, len: usize, ar: &'a Arena) -> Self {
    match Val::quote(ar.val(ty), len, ar) {
      Ok(ty) => Self::PiAnnExpected { ty: ar.term(ty) },
      Err(err) => err.into(),
    }
  }

  pub fn sig_ann_expected<'b>(ty: Val<'b, 'a>, len: usize, ar: &'a Arena) -> Self {
    match Val::quote(ar.val(ty), len, ar) {
      Ok(ty) => Self::SigAnnExpected { ty: ar.term(ty) },
      Err(err) => err.into(),
    }
  }

  pub fn type_mismatch<'b>(
    term: &'a Term<'a>,
    ty: Val<'b, 'a>,
    expect: Val<'b, 'a>,
    len: usize,
    ar: &'a Arena,
  ) -> Self {
    match Val::quote(ar.val(ty), len, ar) {
      Ok(ty) => match Val::quote(ar.val(expect), len, ar) {
        Ok(expect) => Self::TypeMismatch { term, ty: ar.term(ty), ety: ar.term(expect) },
        Err(err) => err.into(),
      },
      Err(err) => err.into(),
    }
  }

  pub fn tup_size_mismatch(term: &'a Term<'a>, sz: usize, esz: usize) -> Self {
    Self::TupSizeMismatch { term, sz, esz }
  }
}

impl<'a> std::convert::From<EvalError<'a>> for TypeError<'a> {
  fn from(err: EvalError<'a>) -> Self {
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

impl std::fmt::Display for EvalError<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::EnvIndex { ix, len } => write!(f, "variable index {ix} out of bound, environment has size {len}"),
      Self::GenLevel { lvl, len } => write!(f, "generic variable level {lvl} out of bound, environment has size {len}"),
      Self::TupInit { n, len } => write!(f, "obtaining initial segment of length {n}, tuple has size {len}"),
      Self::TupLast { n: _, len: _ } => write!(f, "obtaining last element of empty tuple"),
      Self::SigImproper { head } => write!(f, "dependent tuple type must begin with unit, found {head}"),
      Self::TupImproper { head } => write!(f, "dependent tuple value must begin with unit, found {head}"),
    }
  }
}

impl std::fmt::Display for TypeError<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Eval { err } => write!(f, "{err}"),
      Self::UnivForm { univ } => write!(f, "universe {univ} does not have a type"),
      Self::PiForm { from, to } => write!(f, "dependent functions from {from} to {to} are unspecified"),
      Self::SigForm { fst, snd } => write!(f, "dependent tuples with {fst} and {snd} are unspecified"),
      Self::CtxIndex { ix, len } => write!(f, "variable index {ix} out of bound, context has size {len}"),
      Self::SigInit { n, len } => write!(f, "obtaining initial segment of length {n}, tuple type has size {len}"),
      Self::SigLast { n: _, len: _ } => write!(f, "obtaining last element of empty tuple type"),
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
