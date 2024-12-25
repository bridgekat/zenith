use std::fmt::Formatter;
use std::iter::Peekable;

use super::*;

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
  Comma,
  Def,
  Ann,
  Pi,
  Fun,
  Star,
  Unit,
  Type,
  Kind,
  Var(usize),
  Proj(usize),
  Ident(String),
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

/// # Variable bindings
#[derive(Debug, Clone)]
enum Binding {
  Named(String),
  Tuple(Vec<String>),
}

/// # Precedence levels
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Prec {
  Term,
  Body,
  Proj,
  Atom,
}

impl<'a> Term<'a> {
  /// Tokenises `input` into a list of [`Span`].
  pub fn lex(chars: impl Iterator<Item = char>) -> Result<Vec<Span>, LexError> {
    /// Expects the next character to be `c`.
    fn expect(it: &mut impl Iterator<Item = (usize, char)>, c: char) -> Result<(), LexError> {
      match it.next() {
        Some((_, d)) if d == c => Ok(()),
        other => Err(LexError::unexpected(other)),
      }
    }

    let mut it = chars.enumerate().peekable();
    let mut res = Vec::new();
    while let Some((pos, c)) = it.peek().cloned() {
      it.next();
      match c {
        '(' => res.push(Span { tok: Token::LeftParen, start: pos, end: pos + 1 }),
        ')' => res.push(Span { tok: Token::RightParen, start: pos, end: pos + 1 }),
        '[' => res.push(Span { tok: Token::LeftBracket, start: pos, end: pos + 1 }),
        ']' => res.push(Span { tok: Token::RightBracket, start: pos, end: pos + 1 }),
        '{' => {
          if let Some((_, '}')) = it.peek() {
            it.next();
            res.push(Span { tok: Token::Star, start: pos, end: pos + 2 });
          } else {
            res.push(Span { tok: Token::LeftBrace, start: pos, end: pos + 1 });
          }
        }
        '}' => res.push(Span { tok: Token::RightBrace, start: pos, end: pos + 1 }),
        ',' => res.push(Span { tok: Token::Comma, start: pos, end: pos + 1 }),
        '≔' => res.push(Span { tok: Token::Def, start: pos, end: pos + 1 }),
        ':' => {
          if let Some((_, '=')) = it.peek() {
            it.next();
            res.push(Span { tok: Token::Def, start: pos, end: pos + 2 });
          } else {
            res.push(Span { tok: Token::Ann, start: pos, end: pos + 1 });
          }
        }
        '→' => res.push(Span { tok: Token::Pi, start: pos, end: pos + 1 }),
        '-' => {
          expect(&mut it, '>')?;
          res.push(Span { tok: Token::Pi, start: pos, end: pos + 2 });
        }
        '↦' => res.push(Span { tok: Token::Fun, start: pos, end: pos + 1 }),
        '=' => {
          expect(&mut it, '>')?;
          res.push(Span { tok: Token::Fun, start: pos, end: pos + 2 });
        }
        '@' | '^' => {
          let free = c == '@';
          if free {
            expect(&mut it, '^')?;
          }
          let mut len = 1;
          let mut n = 0;
          while let Some((_, c)) = it.peek().cloned() {
            if !c.is_ascii_digit() {
              break;
            }
            it.next();
            len += 1;
            n = n * 10 + c.to_digit(10).unwrap() as usize;
          }
          if free {
            res.push(Span { tok: Token::Var(n), start: pos, end: pos + len });
          } else {
            res.push(Span { tok: Token::Proj(n), start: pos, end: pos + len });
          }
        }
        c if !c.is_whitespace() => {
          let mut len = 1;
          let mut ident = String::new();
          ident.push(c);
          // let ends = "()[]{},≔:=→->↦=>@^";
          let ends = "()[]{},≔:=^";
          while let Some((_, c)) = it.peek().cloned() {
            if c.is_whitespace() || ends.chars().any(|x| x == c) {
              break;
            }
            it.next();
            len += 1;
            ident.push(c);
          }
          match ident.as_str() {
            "Unit" => res.push(Span { tok: Token::Unit, start: pos, end: pos + len }),
            "Type" => res.push(Span { tok: Token::Type, start: pos, end: pos + len }),
            "Kind" => res.push(Span { tok: Token::Kind, start: pos, end: pos + len }),
            _ => res.push(Span { tok: Token::Ident(ident), start: pos, end: pos + len }),
          }
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
  ///
  /// <body> ::=
  ///   | "[" <id> "≔" <term> ("," <id> "≔" <term>)* "]" <body>
  ///   | "[" <id> ":" <term> ("," <id> ":" <term>)* "]" "→" <body>
  ///   | "[" <id> ("," <id>)* "]" "↦" <body>
  ///   | <proj> <proj>*
  ///
  /// <proj> ::=
  ///   | <atom>
  ///   | <proj> "^" <integer>
  ///
  /// <atom> ::=
  ///   | "{}" | "Unit" | "Type" | "Kind" | "@^" <integer> | <id>
  ///   | "(" <term> ")"
  ///   | "{" <id> ":" <term> ("," <id> ":" <term>)* "}"
  ///   | "{" <id> "≔" <term> ("," <id> "≔" <term>)* "}"
  /// ```
  pub fn parse(spans: impl Iterator<Item = Span>, ar: &'a Arena) -> Result<&'a Term<'a>, ParseError> {
    /// Resolves an identifier to a term.
    fn resolve<'a>(x: &str, vars: &[Binding], ar: &'a Arena) -> Option<&'a Term<'a>> {
      for (ix, b) in vars.iter().rev().enumerate() {
        match b {
          Binding::Named(y) if y == x => return Some(ar.term(Term::Var(ix))),
          Binding::Tuple(ys) => {
            if let Some(n) = ys.iter().rev().position(|y| y == x) {
              return Some(ar.term(Term::Last(ar.term(Term::Init(n, ar.term(Term::Var(ix)))))));
            }
          }
          _ => {}
        }
      }
      None
    }

    /// Expects the next token to be `tok`.
    fn expect(it: &mut impl Iterator<Item = Span>, tok: Token) -> Result<(), ParseError> {
      match it.next() {
        Some(s) if s.tok == tok => Ok(()),
        other => Err(ParseError::unexpected(other)),
      }
    }

    /// Expects the next token to be an identifier.
    fn expect_ident(it: &mut impl Iterator<Item = Span>) -> Result<String, ParseError> {
      match it.next() {
        Some(Span { tok: Token::Ident(x), .. }) => Ok(x),
        other => Err(ParseError::unexpected(other)),
      }
    }

    /// Parses a term.
    fn parse_term<'a>(
      it: &mut Peekable<impl Iterator<Item = Span>>,
      vars: &mut Vec<Binding>,
      ar: &'a Arena,
    ) -> Result<&'a Term<'a>, ParseError> {
      let res = parse_body(it, vars, ar)?;
      match it.peek() {
        Some(Span { tok: Token::Ann, .. }) => {
          it.next();
          Ok(ar.term(Term::Ann(res, parse_term(it, vars, ar)?)))
        }
        _ => Ok(res),
      }
    }

    /// Parses a body.
    fn parse_body<'a>(
      it: &mut Peekable<impl Iterator<Item = Span>>,
      vars: &mut Vec<Binding>,
      ar: &'a Arena,
    ) -> Result<&'a Term<'a>, ParseError> {
      match it.peek() {
        // Parsing a binder group (translated into nested binders and a body).
        Some(Span { tok: Token::LeftBracket, .. }) => {
          it.next();
          let x = expect_ident(it)?;
          match it.peek() {
            // Parsing a group of let binders.
            Some(Span { tok: Token::Def, .. }) => {
              it.next();
              let mut vs = Vec::from([parse_term(it, vars, ar)?]);
              vars.push(Binding::Named(x));
              while let Some(Span { tok: Token::Comma, .. }) = it.peek() {
                it.next();
                let x = expect_ident(it)?;
                expect(it, Token::Def)?;
                vs.push(parse_term(it, vars, ar)?);
                vars.push(Binding::Named(x));
              }
              expect(it, Token::RightBracket)?;
              let mut body = parse_body(it, vars, ar)?;
              for v in vs.into_iter().rev() {
                body = ar.term(Term::Let(v, body));
                vars.pop();
              }
              Ok(body)
            }
            // Parsing a group of Pi binders.
            Some(Span { tok: Token::Ann, .. }) => {
              it.next();
              let mut ts = Vec::from([parse_term(it, vars, ar)?]);
              vars.push(Binding::Named(x));
              while let Some(Span { tok: Token::Comma, .. }) = it.peek() {
                it.next();
                let x = expect_ident(it)?;
                expect(it, Token::Ann)?;
                ts.push(parse_term(it, vars, ar)?);
                vars.push(Binding::Named(x));
              }
              expect(it, Token::RightBracket)?;
              expect(it, Token::Pi)?;
              let mut body = parse_body(it, vars, ar)?;
              for t in ts.into_iter().rev() {
                body = ar.term(Term::Pi(t, body));
                vars.pop();
              }
              Ok(body)
            }
            // Parsing a group of function binders.
            _ => {
              let mut ts = Vec::from([()]);
              vars.push(Binding::Named(x));
              while let Some(Span { tok: Token::Comma, .. }) = it.peek() {
                it.next();
                let x = expect_ident(it)?;
                ts.push(());
                vars.push(Binding::Named(x));
              }
              expect(it, Token::RightBracket)?;
              expect(it, Token::Fun)?;
              let mut body = parse_body(it, vars, ar)?;
              for _ in ts.into_iter().rev() {
                body = ar.term(Term::Fun(body));
                vars.pop();
              }
              Ok(body)
            }
          }
        }
        // Parsing a sequence of atomic terms each followed by projections.
        _ => {
          let mut res = parse_proj(it, vars, ar)?;
          loop {
            match it.peek() {
              Some(Span { tok: Token::Star, .. })
              | Some(Span { tok: Token::Unit, .. })
              | Some(Span { tok: Token::Type, .. })
              | Some(Span { tok: Token::Kind, .. })
              | Some(Span { tok: Token::Var(_), .. })
              | Some(Span { tok: Token::Ident(_), .. })
              | Some(Span { tok: Token::LeftParen, .. })
              | Some(Span { tok: Token::LeftBrace, .. }) => {
                res = ar.term(Term::App(res, parse_proj(it, vars, ar)?));
              }
              _ => break Ok(res),
            }
          }
        }
      }
    }

    /// Parses an atomic term followed by a sequence of projections.
    fn parse_proj<'a>(
      it: &mut Peekable<impl Iterator<Item = Span>>,
      vars: &mut Vec<Binding>,
      ar: &'a Arena,
    ) -> Result<&'a Term<'a>, ParseError> {
      let mut res = parse_atom(it, vars, ar)?;
      while let Some(Span { tok: Token::Proj(n), .. }) = it.peek().cloned() {
        it.next();
        res = ar.term(Term::Last(ar.term(Term::Init(n, res))));
      }
      Ok(res)
    }

    /// Parses an atomic term.
    fn parse_atom<'a>(
      it: &mut Peekable<impl Iterator<Item = Span>>,
      vars: &mut Vec<Binding>,
      ar: &'a Arena,
    ) -> Result<&'a Term<'a>, ParseError> {
      match it.peek().cloned() {
        Some(Span { tok: Token::Star, .. }) => {
          it.next();
          Ok(ar.term(Term::Star))
        }
        Some(Span { tok: Token::Unit, .. }) => {
          it.next();
          Ok(ar.term(Term::Unit))
        }
        Some(Span { tok: Token::Type, .. }) => {
          it.next();
          Ok(ar.term(Term::Univ(Univ(0))))
        }
        Some(Span { tok: Token::Kind, .. }) => {
          it.next();
          Ok(ar.term(Term::Univ(Univ(1))))
        }
        Some(Span { tok: Token::Var(n), .. }) => {
          it.next();
          Ok(ar.term(Term::Var(n)))
        }
        Some(Span { tok: Token::Ident(x), start, end }) => {
          it.next();
          resolve(&x, vars, ar).ok_or_else(|| ParseError::undefined_ident(x, start, end))
        }
        Some(Span { tok: Token::LeftParen, .. }) => {
          it.next();
          let res = parse_term(it, vars, ar)?;
          expect(it, Token::RightParen)?;
          Ok(res)
        }
        // Parsing an aggregate (translated into a dependent snoc list).
        Some(Span { tok: Token::LeftBrace, .. }) => {
          it.next();
          let x = expect_ident(it)?;
          match it.peek() {
            // Parsing a tuple aggregate.
            Some(Span { tok: Token::Def, .. }) => {
              it.next();
              vars.push(Binding::Tuple(Vec::new()));
              let mut init = ar.term(Term::Star);
              init = ar.term(Term::Tup(init, parse_term(it, vars, ar)?));
              if let Some(Binding::Tuple(var)) = vars.last_mut() {
                var.push(x);
              }
              while let Some(Span { tok: Token::Comma, .. }) = it.peek() {
                it.next();
                let x = expect_ident(it)?;
                expect(it, Token::Def)?;
                init = ar.term(Term::Tup(init, parse_term(it, vars, ar)?));
                if let Some(Binding::Tuple(var)) = vars.last_mut() {
                  var.push(x);
                }
              }
              expect(it, Token::RightBrace)?;
              vars.pop();
              Ok(init)
            }
            // Parsing a tuple type aggregate.
            Some(Span { tok: Token::Ann, .. }) => {
              it.next();
              vars.push(Binding::Tuple(Vec::new()));
              let mut init = ar.term(Term::Unit);
              init = ar.term(Term::Sig(init, parse_term(it, vars, ar)?));
              if let Some(Binding::Tuple(var)) = vars.last_mut() {
                var.push(x);
              }
              while let Some(Span { tok: Token::Comma, .. }) = it.peek() {
                it.next();
                let x = expect_ident(it)?;
                expect(it, Token::Ann)?;
                init = ar.term(Term::Sig(init, parse_term(it, vars, ar)?));
                if let Some(Binding::Tuple(var)) = vars.last_mut() {
                  var.push(x);
                }
              }
              expect(it, Token::RightBrace)?;
              vars.pop();
              Ok(init)
            }
            _ => Err(ParseError::unexpected(it.next())),
          }
        }
        _ => Err(ParseError::unexpected(it.next())),
      }
    }

    let mut it = spans.peekable();
    parse_term(&mut it, &mut Vec::new(), ar)
  }
}

impl Univ {
  fn print(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    let Univ(u) = *self;
    if u == 0 {
      write!(f, "Type")
    } else {
      write!(f, "Kind")
    }
  }
}

impl Term<'_> {
  /// Pretty-prints a term.
  ///
  /// See documentation of [`Term::parse`] for the BNF grammar.
  fn print(&self, f: &mut Formatter<'_>, count: &mut usize, vars: &mut Vec<Binding>, prec: Prec) -> std::fmt::Result {
    /// Generates a unique lowercase variable name from a unique number.
    fn generate_name(mut id: usize) -> String {
      let mut len = 0;
      let mut m = 1;
      loop {
        len += 1;
        m *= 26;
        if id >= m {
          id -= m;
        } else {
          break;
        }
      }
      let mut res = Vec::new();
      for _ in 0..len {
        res.push(((id % 26) as u8 + b'a') as char);
        id /= 26;
      }
      res.reverse();
      res.into_iter().collect()
    }

    /// Prints a left parenthesis if the actual precedence level is lower than the expected.
    fn left_paren(f: &mut Formatter<'_>, actual: Prec, expected: Prec) -> std::fmt::Result {
      if actual < expected {
        write!(f, "(")?
      }
      Ok(())
    }

    /// Prints a right parenthesis if the actual precedence level is lower than the expected.
    fn right_paren(f: &mut Formatter<'_>, actual: Prec, expected: Prec) -> std::fmt::Result {
      if actual < expected {
        write!(f, ")")?
      }
      Ok(())
    }

    match self {
      Term::Univ(v) => {
        left_paren(f, Prec::Atom, prec)?;
        v.print(f)?;
        right_paren(f, Prec::Atom, prec)?;
        Ok(())
      }
      Term::Var(ix) => {
        if let Some(i) = vars.len().checked_sub(ix + 1) {
          if let Binding::Named(name) = &vars[i] {
            left_paren(f, Prec::Atom, prec)?;
            write!(f, "{}", name)?;
            right_paren(f, Prec::Atom, prec)?;
            return Ok(());
          }
        }
        left_paren(f, Prec::Atom, prec)?;
        write!(f, "@^{}", ix)?;
        right_paren(f, Prec::Atom, prec)?;
        Ok(())
      }
      Term::Ann(x, t) => {
        left_paren(f, Prec::Term, prec)?;
        x.print(f, count, vars, Prec::Body)?;
        write!(f, " : ")?;
        t.print(f, count, vars, Prec::Term)?;
        right_paren(f, Prec::Term, prec)?;
        Ok(())
      }
      Term::Let(_, _) => {
        let mut body = self;
        let mut names = Vec::new();
        let mut vs = Vec::new();
        while let Term::Let(v, x) = body {
          body = x;
          names.push(generate_name(*count));
          *count += 1;
          vs.push(v);
        }
        left_paren(f, Prec::Body, prec)?;
        write!(f, "[")?;
        for (i, (name, t)) in names.iter_mut().zip(vs.iter()).enumerate() {
          if i != 0 {
            write!(f, ", ")?;
          }
          write!(f, "{} ≔ ", name)?;
          t.print(f, count, vars, Prec::Term)?;
          vars.push(Binding::Named(std::mem::take(name)));
        }
        write!(f, "] ")?;
        body.print(f, count, vars, Prec::Body)?;
        right_paren(f, Prec::Body, prec)?;
        vars.truncate(vars.len() - names.len());
        Ok(())
      }
      Term::Pi(_, _) => {
        let mut body = self;
        let mut names = Vec::new();
        let mut ts = Vec::new();
        while let Term::Pi(t, u) = body {
          body = u;
          names.push(generate_name(*count));
          *count += 1;
          ts.push(t);
        }
        left_paren(f, Prec::Body, prec)?;
        write!(f, "[")?;
        for (i, (name, t)) in names.iter_mut().zip(ts.iter()).enumerate() {
          if i != 0 {
            write!(f, ", ")?;
          }
          write!(f, "{} : ", name)?;
          t.print(f, count, vars, Prec::Term)?;
          vars.push(Binding::Named(std::mem::take(name)));
        }
        write!(f, "] → ")?;
        body.print(f, count, vars, Prec::Body)?;
        right_paren(f, Prec::Body, prec)?;
        vars.truncate(vars.len() - names.len());
        Ok(())
      }
      Term::Fun(_) => {
        let mut body = self;
        let mut names = Vec::new();
        while let Term::Fun(b) = body {
          body = b;
          names.push(generate_name(*count));
          *count += 1;
        }
        left_paren(f, Prec::Body, prec)?;
        write!(f, "[")?;
        for (i, name) in names.iter_mut().enumerate() {
          if i != 0 {
            write!(f, ", ")?;
          }
          write!(f, "{}", name)?;
          vars.push(Binding::Named(std::mem::take(name)));
        }
        write!(f, "] ↦ ")?;
        body.print(f, count, vars, Prec::Body)?;
        right_paren(f, Prec::Body, prec)?;
        vars.truncate(vars.len() - names.len());
        Ok(())
      }
      Term::App(_, _) => {
        let mut init = self;
        let mut xs = Vec::new();
        while let Term::App(f, x) = init {
          init = f;
          xs.push(x);
        }
        let g = init;
        xs.reverse();
        left_paren(f, Prec::Body, prec)?;
        g.print(f, count, vars, Prec::Proj)?;
        for x in xs.iter() {
          write!(f, " ")?;
          x.print(f, count, vars, Prec::Proj)?;
        }
        right_paren(f, Prec::Body, prec)?;
        Ok(())
      }
      Term::Unit => write!(f, "Unit"),
      Term::Sig(_, _) => {
        let mut init = self;
        let mut us = Vec::new();
        while let Term::Sig(t, u) = init {
          init = t;
          us.push(u);
        }
        if let Term::Unit = init {
          us.reverse();
          left_paren(f, Prec::Atom, prec)?;
          write!(f, "{{")?;
          vars.push(Binding::Tuple(Vec::new()));
          for (i, t) in us.iter().enumerate() {
            if i != 0 {
              write!(f, ", ")?;
            }
            let name = generate_name(*count);
            *count += 1;
            write!(f, "{} : ", name)?;
            t.print(f, count, vars, Prec::Term)?;
            if let Some(Binding::Tuple(var)) = vars.last_mut() {
              var.push(name);
            }
          }
          vars.pop();
          write!(f, "}}")?;
          right_paren(f, Prec::Atom, prec)?;
        } else {
          write!(f, "<improper tuple type>")?;
        }
        Ok(())
      }
      Term::Star | Term::Tup(_, _) => {
        let mut init = self;
        let mut bs = Vec::new();
        while let Term::Tup(a, b) = init {
          init = a;
          bs.push(b);
        }
        if let Term::Star = init {
          bs.reverse();
          left_paren(f, Prec::Atom, prec)?;
          write!(f, "{{")?;
          vars.push(Binding::Tuple(Vec::new()));
          for (i, b) in bs.iter().enumerate() {
            if i != 0 {
              write!(f, ", ")?;
            }
            let name = generate_name(*count);
            *count += 1;
            write!(f, "{} ≔ ", name)?;
            b.print(f, count, vars, Prec::Term)?;
            if let Some(Binding::Tuple(var)) = vars.last_mut() {
              var.push(name);
            }
          }
          vars.pop();
          write!(f, "}}")?;
          right_paren(f, Prec::Atom, prec)?;
        } else {
          write!(f, "<improper tuple constructor>")?;
        }
        Ok(())
      }
      Term::Last(Term::Init(n, x)) => {
        if let Term::Var(ix) = x {
          if let Some(i) = vars.len().checked_sub(ix + 1) {
            if let Binding::Tuple(var) = &vars[i] {
              if let Some(n) = var.len().checked_sub(n + 1) {
                left_paren(f, Prec::Atom, prec)?;
                write!(f, "{}", var[n])?;
                right_paren(f, Prec::Atom, prec)?;
                return Ok(());
              }
            }
          }
        }
        left_paren(f, Prec::Proj, prec)?;
        x.print(f, count, vars, Prec::Proj)?;
        write!(f, "^{}", n)?;
        right_paren(f, Prec::Proj, prec)?;
        Ok(())
      }
      Term::Init(_, _) => write!(f, "<improper init projection>"),
      Term::Last(_) => write!(f, "<improper last projection>"),
    }
  }
}

impl std::fmt::Display for Univ {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    self.print(f)
  }
}

impl std::fmt::Display for Term<'_> {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    self.print(f, &mut 0, &mut Vec::new(), Prec::Term)
  }
}
