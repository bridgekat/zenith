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
pub enum TypeError<'a> {
  Eval { err: EvalError },
  UnivForm { univ: usize },
  PiForm { from: usize, to: usize },
  SigForm { fst: usize, snd: usize },
  CtxIndex { ix: usize, len: usize },
  SigInit { n: usize, len: usize },
  SigProj { n: usize, len: usize },
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

  /// Clones `self` to given arena.
  pub fn relocate(self, _: &Arena) -> EvalError {
    match self {
      Self::EnvIndex { ix, len } => EvalError::EnvIndex { ix, len },
      Self::GenLevel { lvl, len } => EvalError::GenLevel { lvl, len },
      Self::TupInit { n, len } => EvalError::TupInit { n, len },
      Self::TupProj { n, len } => EvalError::TupProj { n, len },
    }
  }
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

  pub fn sig_init(n: usize, len: usize) -> Self {
    Self::SigInit { n, len }
  }

  pub fn sig_proj(n: usize, len: usize) -> Self {
    Self::SigProj { n, len }
  }

  pub fn ann_expected(term: &'a Term<'a>) -> Self {
    Self::AnnExpected { term }
  }

  pub fn type_expected(term: &'a Term<'a>, ty: Val<'a>, ctx: &Stack<'a>, _env: &Stack<'a>, ar: &'a Arena) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => Self::TypeExpected { term, ty },
      Err(err) => err.into(),
    }
  }

  pub fn pi_expected(term: &'a Term<'a>, ty: Val<'a>, ctx: &Stack<'a>, _env: &Stack<'a>, ar: &'a Arena) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => Self::PiExpected { term, ty },
      Err(err) => err.into(),
    }
  }

  pub fn sig_expected(term: &'a Term<'a>, ty: Val<'a>, ctx: &Stack<'a>, _env: &Stack<'a>, ar: &'a Arena) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => Self::SigExpected { term, ty },
      Err(err) => err.into(),
    }
  }

  pub fn pi_ann_expected(ty: Val<'a>, ctx: &Stack<'a>, _env: &Stack<'a>, ar: &'a Arena) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => Self::PiAnnExpected { ty },
      Err(err) => err.into(),
    }
  }

  pub fn sig_ann_expected(ty: Val<'a>, ctx: &Stack<'a>, _env: &Stack<'a>, ar: &'a Arena) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => Self::SigAnnExpected { ty },
      Err(err) => err.into(),
    }
  }

  pub fn type_mismatch(
    term: &'a Term<'a>,
    ty: Val<'a>,
    ety: Val<'a>,
    ctx: &Stack<'a>,
    _env: &Stack<'a>,
    ar: &'a Arena,
  ) -> Self {
    match ar.val(ty).quote(ctx.len(), ar) {
      Ok(ty) => match ar.val(ety).quote(ctx.len(), ar) {
        Ok(ety) => Self::TypeMismatch { term, ty, ety },
        Err(err) => err.into(),
      },
      Err(err) => err.into(),
    }
  }

  pub fn tup_size_mismatch(term: &'a Term<'a>, sz: usize, esz: usize) -> Self {
    Self::TupSizeMismatch { term, sz, esz }
  }

  /// Clones `self` to given arena.
  pub fn relocate(self, ar: &Arena) -> TypeError {
    match self {
      Self::Eval { err } => TypeError::Eval { err: err.relocate(ar) },
      Self::UnivForm { univ } => TypeError::UnivForm { univ },
      Self::PiForm { from, to } => TypeError::PiForm { from, to },
      Self::SigForm { fst, snd } => TypeError::SigForm { fst, snd },
      Self::CtxIndex { ix, len } => TypeError::CtxIndex { ix, len },
      Self::SigInit { n, len } => TypeError::SigInit { n, len },
      Self::SigProj { n, len } => TypeError::SigProj { n, len },
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

impl std::fmt::Display for TypeError<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Eval { err } => write!(f, "{err}"),
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
