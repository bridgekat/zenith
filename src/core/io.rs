use std::iter::Peekable;
use std::vec::IntoIter;

use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
  LeftParen,
  RightParen,
  LeftBracket,
  RightBracket,
  Colon,
  ColonEq,
  Pi,
  Fun,
  Sig,
  Pair,
  Type,
  Kind,
  Fst,
  Snd,
  Unit,
  Star,
  Free(usize),
  Ident(String),
}

#[derive(Debug, Clone)]
pub struct Span {
  pub tok: Token,
  pub start: usize,
  pub end: usize,
}

impl<'a> Term<'a> {
  pub fn lex(input: &str) -> Result<Vec<Span>, LexError> {
    fn expect(it: &mut impl Iterator<Item = (usize, char)>, c: char) -> Result<(), LexError> {
      match it.next() {
        Some((_, d)) if d == c => Ok(()),
        other => Err(LexError::unexpected(other)),
      }
    }
    let mut it = input.chars().enumerate().peekable();
    let mut res = Vec::new();
    while let Some((pos, c)) = it.next() {
      match c {
        '(' => res.push(Span { tok: Token::LeftParen, start: pos, end: pos + 1 }),
        ')' => res.push(Span { tok: Token::RightParen, start: pos, end: pos + 1 }),
        '[' => {
          if let Some((_, ']')) = it.peek().cloned() {
            it.next();
            res.push(Span { tok: Token::Star, start: pos, end: pos + 2 });
          } else {
            res.push(Span { tok: Token::LeftBracket, start: pos, end: pos + 1 });
          }
        }
        ']' => res.push(Span { tok: Token::RightBracket, start: pos, end: pos + 1 }),
        ':' => {
          if let Some((_, '=')) = it.peek().cloned() {
            it.next();
            res.push(Span { tok: Token::ColonEq, start: pos, end: pos + 2 });
          } else {
            res.push(Span { tok: Token::Colon, start: pos, end: pos + 1 });
          }
        }
        '-' => {
          expect(&mut it, '>')?;
          res.push(Span { tok: Token::Pi, start: pos, end: pos + 2 });
        }
        '=' => {
          expect(&mut it, '>')?;
          res.push(Span { tok: Token::Fun, start: pos, end: pos + 2 });
        }
        '*' => res.push(Span { tok: Token::Sig, start: pos, end: pos + 1 }),
        ',' => res.push(Span { tok: Token::Pair, start: pos, end: pos + 1 }),
        '^' => {
          let mut len = 1;
          let mut n = 0;
          while let Some((_, c)) = it.peek().cloned() {
            if c.is_ascii_digit() {
              it.next();
              len += 1;
              n = n * 10 + c.to_digit(10).unwrap() as usize;
            } else {
              break;
            }
          }
          res.push(Span { tok: Token::Free(n), start: pos, end: pos + len });
        }
        c if c.is_alphabetic() => {
          let mut len = 1;
          let mut ident = String::new();
          ident.push(c);
          while let Some((_, c)) = it.peek().cloned() {
            if c.is_alphanumeric() || c == '_' {
              it.next();
              len += 1;
              ident.push(c);
            } else {
              break;
            }
          }
          match ident.as_str() {
            "Type" => res.push(Span { tok: Token::Type, start: pos, end: pos + len }),
            "Kind" => res.push(Span { tok: Token::Kind, start: pos, end: pos + len }),
            "Fst" => res.push(Span { tok: Token::Fst, start: pos, end: pos + len }),
            "Snd" => res.push(Span { tok: Token::Snd, start: pos, end: pos + len }),
            "Unit" => res.push(Span { tok: Token::Unit, start: pos, end: pos + len }),
            _ => res.push(Span { tok: Token::Ident(ident), start: pos, end: pos + len }),
          }
        }
        c if c.is_whitespace() => {}
        c => return Err(LexError::unexpected(Some((pos, c)))),
      }
    }
    Ok(res)
  }

  pub fn parse(spans: Vec<Span>, ar: &'a Arena<'a>) -> Result<&'a Term<'a>, ParseError> {
    fn expect(it: &mut Peekable<IntoIter<Span>>, tok: Token) -> Result<(), ParseError> {
      match it.next() {
        Some(s) if s.tok == tok => Ok(()),
        other => Err(ParseError::unexpected(other)),
      }
    }
    fn parse_binder<'a>(
      it: &mut Peekable<IntoIter<Span>>,
      vars: &mut Vec<String>,
      ar: &'a Arena<'a>,
    ) -> Result<(String, Option<&'a Term<'a>>, Option<&'a Term<'a>>), ParseError> {
      let x = match it.next() {
        Some(Span { tok: Token::Ident(x), .. }) => x,
        other => return Err(ParseError::unexpected(other)),
      };
      let (t, v) = match it.peek() {
        Some(Span { tok: Token::Colon, .. }) => {
          expect(it, Token::Colon)?;
          (Some(parse_term(it, vars, ar)?), None)
        }
        Some(Span { tok: Token::ColonEq, .. }) => {
          expect(it, Token::ColonEq)?;
          (None, Some(parse_term(it, vars, ar)?))
        }
        _ => (None, None),
      };
      Ok((x, t, v))
    }
    fn try_parse_arg<'a>(
      it: &mut Peekable<IntoIter<Span>>,
      vars: &mut Vec<String>,
      ar: &'a Arena<'a>,
    ) -> Result<Option<&'a Term<'a>>, ParseError> {
      match it.peek().cloned() {
        Some(Span { tok: Token::LeftBracket, .. }) => {
          expect(it, Token::LeftBracket)?;
          let (x, t, v) = parse_binder(it, vars, ar)?;
          expect(it, Token::RightBracket)?;
          match (t, v) {
            (Some(_), Some(_)) => unreachable!(),
            (Some(t), None) => match it.peek() {
              Some(Span { tok: Token::Pi, .. }) => {
                expect(it, Token::Pi)?;
                vars.push(x);
                let b = parse_term(it, vars, ar)?;
                vars.pop();
                Ok(Some(ar.term(Term::Pi(t, b))))
              }
              Some(Span { tok: Token::Sig, .. }) => {
                expect(it, Token::Sig)?;
                vars.push(x);
                let b = parse_term(it, vars, ar)?;
                vars.pop();
                Ok(Some(ar.term(Term::Sig(t, b))))
              }
              _ => Err(ParseError::unexpected(it.next())),
            },
            (None, Some(v)) => match it.peek() {
              Some(Span { tok: Token::Pair, .. }) => {
                expect(it, Token::Pair)?;
                vars.push(x);
                let b = parse_term(it, vars, ar)?;
                vars.pop();
                Ok(Some(ar.term(Term::Pair(v, b))))
              }
              _ => {
                vars.push(x);
                let b = parse_term(it, vars, ar)?;
                vars.pop();
                Ok(Some(ar.term(Term::Let(v, b))))
              }
            },
            (None, None) => {
              expect(it, Token::Fun)?;
              vars.push(x);
              let b = parse_term(it, vars, ar)?;
              vars.pop();
              Ok(Some(ar.term(Term::Fun(b))))
            }
          }
        }
        Some(Span { tok: Token::LeftParen, .. }) => {
          expect(it, Token::LeftParen)?;
          let x = parse_term(it, vars, ar)?;
          expect(it, Token::RightParen)?;
          Ok(Some(x))
        }
        Some(Span { tok: Token::Type, .. }) => {
          expect(it, Token::Type)?;
          Ok(Some(ar.term(Term::Univ(Univ(0)))))
        }
        Some(Span { tok: Token::Kind, .. }) => {
          expect(it, Token::Kind)?;
          Ok(Some(ar.term(Term::Univ(Univ(1)))))
        }
        Some(Span { tok: Token::Fst, .. }) => {
          expect(it, Token::Fst)?;
          Ok(Some(ar.term(Term::Fst(parse_term(it, vars, ar)?))))
        }
        Some(Span { tok: Token::Snd, .. }) => {
          expect(it, Token::Snd)?;
          Ok(Some(ar.term(Term::Snd(parse_term(it, vars, ar)?))))
        }
        Some(Span { tok: Token::Unit, .. }) => {
          expect(it, Token::Unit)?;
          Ok(Some(ar.term(Term::Unit)))
        }
        Some(Span { tok: Token::Star, .. }) => {
          expect(it, Token::Star)?;
          Ok(Some(ar.term(Term::Star)))
        }
        Some(Span { tok: Token::Free(n), .. }) => {
          it.next();
          Ok(Some(ar.term(Term::Var(vars.len() + n))))
        }
        Some(Span { tok: Token::Ident(x), start, end }) => {
          it.next();
          match vars.iter().position(|y| y == &x) {
            Some(lvl) => Ok(Some(ar.term(Term::Var(vars.len() - lvl - 1)))),
            None => Err(ParseError::undefined_ident(x, start, end)),
          }
        }
        _ => Ok(None),
      }
    }
    fn parse_term<'a>(
      it: &mut Peekable<IntoIter<Span>>,
      vars: &mut Vec<String>,
      ar: &'a Arena<'a>,
    ) -> Result<&'a Term<'a>, ParseError> {
      let mut args = Vec::new();
      while let Some(arg) = try_parse_arg(it, vars, ar)? {
        args.push(arg);
      }
      args.reverse();
      let mut res = match args.pop() {
        Some(x) => x,
        None => return Err(ParseError::unexpected(it.next())),
      };
      while let Some(arg) = args.pop() {
        res = ar.term(Term::App(res, arg));
      }
      match it.peek() {
        Some(Span { tok: Token::Colon, .. }) => {
          expect(it, Token::Colon)?;
          let ty = parse_term(it, vars, ar)?;
          Ok(ar.term(Term::Ann(res, ty)))
        }
        _ => Ok(res),
      }
    }
    let mut it = spans.into_iter().peekable();
    let res = parse_term(&mut it, &mut Vec::new(), ar)?;
    match it.peek() {
      Some(_) => Err(ParseError::unexpected(it.next())),
      _ => Ok(res),
    }
  }
}

impl Univ {
  fn print(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let Univ(u) = *self;
    if u == 0 {
      write!(f, "Type")
    } else {
      write!(f, "Kind")
    }
  }
}

impl Term<'_> {
  fn print(&self, count: &mut usize, names: &mut Vec<usize>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    // Generates a unique lowercase variable name from a unique number.
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
      let mut res = String::new();
      for _ in 0..len {
        res.insert(0, ((id % 26) as u8 + b'a') as char);
        id /= 26;
      }
      res
    }
    match self {
      Term::Univ(univ) => write!(f, "{univ}"),
      Term::Var(ix) => match *ix < names.len() {
        true => write!(f, "{}", generate_name(names[names.len() - 1 - ix])),
        false => write!(f, "^{}", ix - names.len()),
      },
      Term::Ann(x, t) => {
        write!(f, "(")?;
        x.print(count, names, f)?;
        write!(f, ") : (")?;
        t.print(count, names, f)?;
        write!(f, ")")?;
        Ok(())
      }
      Term::Let(v, x) => {
        let c = *count;
        *count += 1;
        write!(f, "[{} := ", generate_name(c))?;
        v.print(count, names, f)?;
        write!(f, "] ")?;
        names.push(c);
        x.print(count, names, f)?;
        names.pop();
        Ok(())
      }
      Term::Pi(s, t) => {
        let c = *count;
        *count += 1;
        write!(f, "[{} : ", generate_name(c))?;
        s.print(count, names, f)?;
        write!(f, "] -> ")?;
        names.push(c);
        t.print(count, names, f)?;
        names.pop();
        Ok(())
      }
      Term::Fun(b) => {
        let c = *count;
        *count += 1;
        write!(f, "[{}] => ", generate_name(c))?;
        names.push(c);
        b.print(count, names, f)?;
        names.pop();
        Ok(())
      }
      Term::App(g, x) => {
        write!(f, "(")?;
        g.print(count, names, f)?;
        write!(f, ") (")?;
        x.print(count, names, f)?;
        write!(f, ")")?;
        Ok(())
      }
      Term::Sig(s, t) => {
        let c = *count;
        *count += 1;
        write!(f, "[{} : ", generate_name(c))?;
        s.print(count, names, f)?;
        write!(f, "] * ")?;
        names.push(c);
        t.print(count, names, f)?;
        names.pop();
        Ok(())
      }
      Term::Pair(a, b) => {
        let c = *count;
        *count += 1;
        write!(f, "[{} := ", generate_name(c))?;
        a.print(count, names, f)?;
        write!(f, "], ")?;
        names.push(c);
        b.print(count, names, f)?;
        names.pop();
        Ok(())
      }
      Term::Fst(x) => {
        write!(f, "Fst (")?;
        x.print(count, names, f)?;
        write!(f, ")")?;
        Ok(())
      }
      Term::Snd(x) => {
        write!(f, "Snd (")?;
        x.print(count, names, f)?;
        write!(f, ")")?;
        Ok(())
      }
      Term::Unit => write!(f, "Unit"),
      Term::Star => write!(f, "[]"),
    }
  }
}

impl std::fmt::Display for Univ {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.print(f)
  }
}

impl std::fmt::Display for Term<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.print(&mut 0, &mut Vec::new(), f)
  }
}
