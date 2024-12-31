use std::iter::Peekable;

use super::*;
use crate::arena::Arena;
use crate::term::{Binder, Term};

/// # Lexer tokens
///
/// Produced by the simple lexer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
  LeftParen,
  RightParen,
  LeftBracket,
  RightBracket,
  LeftBrace,
  RightBrace,
  Sep,
  Dot,
  Env,
  Pi,
  Fun,
  Def,
  Ann(bool),
  Unit,
  Type,
  Kind,
  Ix(usize),
  Id(String),
}

/// # Lexer spans
///
/// Tokens together with their positions in the input string.
#[derive(Debug, Clone)]
pub struct Span {
  pub tok: Token,
  pub start: usize,
  pub end: usize,
}

impl<'a> Term<'a, Named<'a>> {
  /// Tokenises `input` into a list of [`Span`].
  pub fn lex(chars: impl Iterator<Item = char>) -> Result<Vec<Span>, LexError> {
    // The token grammar is almost LL(1).
    let mut it = chars.enumerate().peekable();
    let mut res = Vec::new();
    // The first character can be taken unconditionally.
    while let Some((pos, c)) = it.next() {
      match c {
        '(' => res.push(Span { tok: Token::LeftParen, start: pos, end: pos + 1 }),
        ')' => res.push(Span { tok: Token::RightParen, start: pos, end: pos + 1 }),
        '[' => res.push(Span { tok: Token::LeftBracket, start: pos, end: pos + 1 }),
        ']' => res.push(Span { tok: Token::RightBracket, start: pos, end: pos + 1 }),
        '{' => res.push(Span { tok: Token::LeftBrace, start: pos, end: pos + 1 }),
        '}' => res.push(Span { tok: Token::RightBrace, start: pos, end: pos + 1 }),
        ',' => res.push(Span { tok: Token::Sep, start: pos, end: pos + 1 }),
        '.' => res.push(Span { tok: Token::Dot, start: pos, end: pos + 1 }),
        '^' => {
          let mut len = 1;
          let mut n = 0;
          while let Some((_, d)) = it.peek().cloned() {
            if !d.is_ascii_digit() {
              break;
            }
            it.next();
            len += 1;
            n = n * 10 + d.to_digit(10).unwrap() as usize;
          }
          let tok = Token::Ix(n);
          res.push(Span { tok, start: pos, end: pos + len });
        }
        c if !c.is_whitespace() => {
          let mut len = 1;
          let mut s = String::new();
          s.push(c);
          while let Some((_, d)) = it.peek().cloned() {
            if d.is_whitespace() || "()[]{},.^".chars().any(|x| x == d) {
              break;
            }
            it.next();
            len += 1;
            s.push(d);
          }
          let tok = match s.as_str() {
            "@" => Token::Env,
            "→" | "->" => Token::Pi,
            "↦" | "=>" => Token::Fun,
            "≔" | ":=" => Token::Def,
            ":" => Token::Ann(false),
            "::" => Token::Ann(true),
            "Unit" => Token::Unit,
            "Type" => Token::Type,
            "Kind" => Token::Kind,
            _ => Token::Id(s),
          };
          res.push(Span { tok, start: pos, end: pos + len });
        }
        _ => {}
      }
    }
    Ok(res)
  }

  /// Parses a list of [`Span`] into a [`Term`].
  ///
  /// The grammar is given by the following BNF:
  ///
  /// ```bnf
  /// <term> ::=
  ///   | <body>
  ///   | <body> ":" <term>
  ///   | <body> "::" <term>
  ///
  /// <body> ::=
  ///   | "[" <id> "≔" <term> ("," <id> "≔" <term>)* "]" <body>
  ///   | "[" <id> ":" <term> ("," <id> ":" <term>)* "]" "→" <body>
  ///   | "[" <id> ("," <id>)* "]" "↦" <body>
  ///   | <proj> <proj>*
  ///
  /// <proj> ::=
  ///   | <atom>
  ///   | <proj> <index>
  ///   | <proj> "." <atom>
  ///
  /// <atom> ::=
  ///   | "{" "}" | "Unit" | "Type" | "Kind" | "@" <index> | <id>
  ///   | "(" <term> ")"
  ///   | "{" <id> ":" <term> ("," <id> ":" <term>)* "}"
  ///   | "{" <id> "≔" <term> ("," <id> "≔" <term>)* "}"
  /// ```
  pub fn parse(spans: impl Iterator<Item = Span>, ar: &'a Arena) -> Result<&'a Term<'a, Named<'a>>, ParseError> {
    /// Expects the next token to have the same kind as `tok`.
    fn expect(it: &mut impl Iterator<Item = Span>, tok: Token) -> Result<(), ParseError> {
      match it.next() {
        Some(s) if std::mem::discriminant(&s.tok) == std::mem::discriminant(&tok) => Ok(()),
        other => Err(ParseError::unexpected(other)),
      }
    }
    /// Expects the next token to be a de Bruijn index.
    fn expect_ix(it: &mut impl Iterator<Item = Span>) -> Result<usize, ParseError> {
      match it.next() {
        Some(Span { tok: Token::Ix(n), .. }) => Ok(n),
        other => Err(ParseError::unexpected(other)),
      }
    }
    /// Expects the next token to be an identifier. Also returns the starting and ending positions.
    fn expect_id(it: &mut impl Iterator<Item = Span>) -> Result<(String, usize, usize), ParseError> {
      match it.next() {
        Some(Span { tok: Token::Id(x), start, end }) => Ok((x, start, end)),
        other => Err(ParseError::unexpected(other)),
      }
    }
    /// Parses a term.
    fn parse_term<'a>(
      it: &mut Peekable<impl Iterator<Item = Span>>,
      ar: &'a Arena,
    ) -> Result<&'a Term<'a, Named<'a>>, ParseError> {
      // Parsing a term body.
      let res = parse_body(it, ar)?;
      match it.peek() {
        // Parsing an optional type annotation.
        Some(Span { tok: Token::Ann(false), .. }) => {
          it.next();
          Ok(ar.term(Term::Ann(res, parse_term(it, ar)?, false)))
        }
        // Parsing an optional type annotation with double colons (indicating an arena boundary).
        Some(Span { tok: Token::Ann(true), .. }) => {
          it.next();
          Ok(ar.term(Term::Ann(res, parse_term(it, ar)?, true)))
        }
        _ => Ok(res),
      }
    }
    /// Parses a term body.
    fn parse_body<'a>(
      it: &mut Peekable<impl Iterator<Item = Span>>,
      ar: &'a Arena,
    ) -> Result<&'a Term<'a, Named<'a>>, ParseError> {
      match it.peek() {
        // Parsing a binder group.
        Some(Span { tok: Token::LeftBracket, .. }) => {
          it.next();
          // Parsing a non-empty binder group.
          let (x, _, _) = expect_id(it)?;
          match it.peek() {
            // Parsing a group of let binders.
            Some(Span { tok: Token::Def, .. }) => {
              it.next();
              let mut is = Vec::from([Binder { name: ar.string(&x), attrs: &[] }]);
              let mut vs = Vec::from([parse_term(it, ar)?]);
              while let Some(Span { tok: Token::Sep, .. }) = it.peek() {
                it.next();
                let (x, _, _) = expect_id(it)?;
                expect(it, Token::Def)?;
                is.push(Binder { name: ar.string(&x), attrs: &[] });
                vs.push(parse_term(it, ar)?);
              }
              expect(it, Token::RightBracket)?;
              let mut body = parse_body(it, ar)?;
              for (i, v) in is.into_iter().rev().zip(vs.into_iter().rev()) {
                body = ar.term(Term::Let(i, v, body));
              }
              Ok(body)
            }
            // Parsing a group of Pi binders.
            Some(Span { tok: Token::Ann(_), .. }) => {
              it.next();
              let mut is = Vec::from([Binder { name: ar.string(&x), attrs: &[] }]);
              let mut ts = Vec::from([parse_term(it, ar)?]);
              while let Some(Span { tok: Token::Sep, .. }) = it.peek() {
                it.next();
                let (x, _, _) = expect_id(it)?;
                expect(it, Token::Ann(false))?;
                is.push(Binder { name: ar.string(&x), attrs: &[] });
                ts.push(parse_term(it, ar)?);
              }
              expect(it, Token::RightBracket)?;
              expect(it, Token::Pi)?;
              let mut body = parse_body(it, ar)?;
              for (i, t) in is.into_iter().rev().zip(ts.into_iter().rev()) {
                body = ar.term(Term::Pi(i, t, body));
              }
              Ok(body)
            }
            // Parsing a group of function binders.
            _ => {
              let mut is = Vec::from([Binder { name: ar.string(&x), attrs: &[] }]);
              let mut ts = Vec::from([()]);
              while let Some(Span { tok: Token::Sep, .. }) = it.peek() {
                it.next();
                let (x, _, _) = expect_id(it)?;
                is.push(Binder { name: ar.string(&x), attrs: &[] });
                ts.push(());
              }
              expect(it, Token::RightBracket)?;
              expect(it, Token::Fun)?;
              let mut body = parse_body(it, ar)?;
              for (i, _) in is.into_iter().rev().zip(ts.into_iter().rev()) {
                body = ar.term(Term::Fun(i, body));
              }
              Ok(body)
            }
          }
        }
        // Parsing a sequence of atomic terms, each followed by a sequence of projections.
        _ => {
          // Parsing the first atomic term.
          let mut res = parse_proj(it, ar)?;
          loop {
            match it.peek() {
              // Parsing the next atomic term.
              Some(Span { tok: Token::Unit, .. })
              | Some(Span { tok: Token::Type, .. })
              | Some(Span { tok: Token::Kind, .. })
              | Some(Span { tok: Token::Env, .. })
              | Some(Span { tok: Token::Id(_), .. })
              | Some(Span { tok: Token::LeftParen, .. })
              | Some(Span { tok: Token::LeftBrace, .. }) => {
                res = ar.term(Term::App(res, parse_proj(it, ar)?, false));
              }
              _ => break Ok(res),
            }
          }
        }
      }
    }
    /// Parses an atomic term followed by a sequence of projections and dot-applications.
    fn parse_proj<'a>(
      it: &mut Peekable<impl Iterator<Item = Span>>,
      ar: &'a Arena,
    ) -> Result<&'a Term<'a, Named<'a>>, ParseError> {
      let mut res = parse_atom(it, ar)?;
      loop {
        match it.peek() {
          Some(Span { tok: Token::Ix(_), .. }) => {
            res = ar.term(Term::Last(ar.term(Term::Init(expect_ix(it)?, res))));
          }
          Some(Span { tok: Token::Dot, .. }) => {
            it.next();
            res = ar.term(Term::App(parse_atom(it, ar)?, res, true));
          }
          _ => break Ok(res),
        }
      }
    }
    /// Parses an atomic term.
    fn parse_atom<'a>(
      it: &mut Peekable<impl Iterator<Item = Span>>,
      ar: &'a Arena,
    ) -> Result<&'a Term<'a, Named<'a>>, ParseError> {
      // All atoms begin with a terminal token that can be taken unconditionally.
      match it.next() {
        // Parsing a single token.
        Some(Span { tok: Token::Unit, .. }) => Ok(ar.term(Term::Unit)),
        Some(Span { tok: Token::Type, .. }) => Ok(ar.term(Term::Univ(0))),
        Some(Span { tok: Token::Kind, .. }) => Ok(ar.term(Term::Univ(1))),
        Some(Span { tok: Token::Env, .. }) => Ok(ar.term(Term::Var(Var::Ix(expect_ix(it)?)))),
        Some(Span { tok: Token::Id(x), start, end }) => Ok(ar.term(Term::Var(Var::Name(ar.string(&x), start, end)))),
        // Parsing a parenthesised term.
        Some(Span { tok: Token::LeftParen, .. }) => {
          let res = parse_term(it, ar)?;
          expect(it, Token::RightParen)?;
          Ok(res)
        }
        // Parsing an aggregate (translated into a dependent snoc list).
        Some(Span { tok: Token::LeftBrace, .. }) => {
          // Parsing an empty aggregate.
          if let Some(Span { tok: Token::RightBrace, .. }) = it.peek() {
            it.next();
            return Ok(ar.term(Term::Star));
          }
          // Parsing a non-empty aggregate.
          let (x, _, _) = expect_id(it)?;
          // The next token can be taken unconditionally.
          match it.next() {
            // Parsing a tuple aggregate.
            Some(Span { tok: Token::Def, .. }) => {
              let mut init = ar.term(Term::Star);
              init = ar.term(Term::Tup(Binder { name: ar.string(&x), attrs: &[] }, init, parse_term(it, ar)?));
              while let Some(Span { tok: Token::Sep, .. }) = it.peek() {
                it.next();
                let (x, _, _) = expect_id(it)?;
                expect(it, Token::Def)?;
                init = ar.term(Term::Tup(Binder { name: ar.string(&x), attrs: &[] }, init, parse_term(it, ar)?));
              }
              expect(it, Token::RightBrace)?;
              Ok(init)
            }
            // Parsing a tuple type aggregate.
            Some(Span { tok: Token::Ann(_), .. }) => {
              let mut init = ar.term(Term::Unit);
              init = ar.term(Term::Sig(Binder { name: ar.string(&x), attrs: &[] }, init, parse_term(it, ar)?));
              while let Some(Span { tok: Token::Sep, .. }) = it.peek() {
                it.next();
                let (x, _, _) = expect_id(it)?;
                expect(it, Token::Ann(false))?;
                init = ar.term(Term::Sig(Binder { name: ar.string(&x), attrs: &[] }, init, parse_term(it, ar)?));
              }
              expect(it, Token::RightBrace)?;
              Ok(init)
            }
            other => Err(ParseError::unexpected(other)),
          }
        }
        other => Err(ParseError::unexpected(other)),
      }
    }
    // The term grammar is LL(1).
    let mut it = spans.peekable();
    parse_term(&mut it, ar)
  }
}
