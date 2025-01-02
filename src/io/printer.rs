use std::fmt::Formatter;

use crate::elab::Term;

/// Precedence levels.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Prec {
  Term,
  Body,
  Proj,
  Atom,
}

impl Term<'_> {
  /// Pretty-prints a term.
  ///
  /// See documentation of [`Term::parse`] for the BNF grammar.
  fn print(&self, f: &mut Formatter<'_>, prec: Prec) -> std::fmt::Result {
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
    /// Converts an empty string to "_".
    fn present_name(x: &str) -> &str {
      if x.is_empty() {
        "_"
      } else {
        x
      }
    }
    match self {
      Term::Univ(v) => {
        left_paren(f, Prec::Atom, prec)?;
        match v {
          0 => write!(f, "Type")?,
          1 => write!(f, "Kind")?,
          _ => write!(f, "<unsupported universe level>")?,
        };
        right_paren(f, Prec::Atom, prec)?;
        Ok(())
      }
      Term::Var(ix) => {
        left_paren(f, Prec::Atom, prec)?;
        write!(f, "@^{}", ix)?;
        right_paren(f, Prec::Atom, prec)?;
        Ok(())
      }
      Term::Ann(x, t, b) => {
        left_paren(f, Prec::Term, prec)?;
        x.print(f, Prec::Body)?;
        match b {
          false => write!(f, " : ")?,
          true => write!(f, " :: ")?,
        }
        t.print(f, Prec::Term)?;
        right_paren(f, Prec::Term, prec)?;
        Ok(())
      }
      Term::Let(_, _, _) => {
        let mut body = self;
        let mut vs = Vec::new();
        while let Term::Let(i, v, x) = body {
          body = x;
          vs.push((i, v));
        }
        left_paren(f, Prec::Body, prec)?;
        write!(f, "[")?;
        for (j, (i, t)) in vs.iter().enumerate() {
          if j != 0 {
            write!(f, ", ")?;
          }
          write!(f, "{} ≔ ", present_name(i.name))?;
          t.print(f, Prec::Term)?;
        }
        write!(f, "] ")?;
        body.print(f, Prec::Body)?;
        right_paren(f, Prec::Body, prec)?;
        Ok(())
      }
      Term::Pi(_, _, _) => {
        let mut body = self;
        let mut ts = Vec::new();
        while let Term::Pi(i, t, u) = body {
          body = u;
          ts.push((i, t));
        }
        left_paren(f, Prec::Body, prec)?;
        write!(f, "[")?;
        for (j, (i, t)) in ts.iter().enumerate() {
          if j != 0 {
            write!(f, ", ")?;
          }
          write!(f, "{} : ", present_name(i.name))?;
          t.print(f, Prec::Term)?;
        }
        write!(f, "] → ")?;
        body.print(f, Prec::Body)?;
        right_paren(f, Prec::Body, prec)?;
        Ok(())
      }
      Term::Fun(_, _) => {
        let mut body = self;
        let mut is = Vec::new();
        while let Term::Fun(i, b) = body {
          body = b;
          is.push(i);
        }
        left_paren(f, Prec::Body, prec)?;
        write!(f, "[")?;
        for (j, i) in is.iter().enumerate() {
          if j != 0 {
            write!(f, ", ")?;
          }
          write!(f, "{}", present_name(i.name))?;
        }
        write!(f, "] ↦ ")?;
        body.print(f, Prec::Body)?;
        right_paren(f, Prec::Body, prec)?;
        Ok(())
      }
      Term::App(_, _, _) => {
        let mut init = self;
        let mut xs = Vec::new();
        while let Term::App(f, x, _) = init {
          init = f;
          xs.push(x);
        }
        let g = init;
        xs.reverse();
        left_paren(f, Prec::Body, prec)?;
        g.print(f, Prec::Proj)?;
        for x in xs.iter() {
          write!(f, " ")?;
          x.print(f, Prec::Proj)?;
        }
        right_paren(f, Prec::Body, prec)?;
        Ok(())
      }
      Term::Unit => write!(f, "Unit"),
      Term::Sig(_, _, _) => {
        let mut init = self;
        let mut us = Vec::new();
        while let Term::Sig(i, t, u) = init {
          init = t;
          us.push((i, u));
        }
        if let Term::Unit = init {
          us.reverse();
          left_paren(f, Prec::Atom, prec)?;
          write!(f, "{{")?;
          for (j, (i, u)) in us.iter().enumerate() {
            if j != 0 {
              write!(f, ", ")?;
            }
            write!(f, "{} : ", present_name(i.name))?;
            u.print(f, Prec::Term)?;
          }
          write!(f, "}}")?;
          right_paren(f, Prec::Atom, prec)?;
        } else {
          write!(f, "<improper tuple type>")?;
        }
        Ok(())
      }
      Term::Star | Term::Tup(_, _, _) => {
        let mut init = self;
        let mut bs = Vec::new();
        while let Term::Tup(i, a, b) = init {
          init = a;
          bs.push((i, b));
        }
        if let Term::Star = init {
          bs.reverse();
          left_paren(f, Prec::Atom, prec)?;
          write!(f, "{{")?;
          for (j, (i, b)) in bs.iter().enumerate() {
            if j != 0 {
              write!(f, ", ")?;
            }
            write!(f, "{} ≔ ", present_name(i.name))?;
            b.print(f, Prec::Term)?;
          }
          write!(f, "}}")?;
          right_paren(f, Prec::Atom, prec)?;
        } else {
          write!(f, "<improper tuple constructor>")?;
        }
        Ok(())
      }
      Term::Last(Term::Init(n, x)) => {
        left_paren(f, Prec::Proj, prec)?;
        x.print(f, Prec::Proj)?;
        write!(f, "^{}", n)?;
        right_paren(f, Prec::Proj, prec)?;
        Ok(())
      }
      Term::Init(_, _) => write!(f, "<improper init projection>"),
      Term::Last(_) => write!(f, "<improper last projection>"),
      Term::Meta(_) => todo!(),
      Term::Name(name) => {
        left_paren(f, Prec::Atom, prec)?;
        write!(f, "{}", name.segments.join("::"))?;
        right_paren(f, Prec::Atom, prec)?;
        Ok(())
      }
    }
  }
}

impl std::fmt::Display for Term<'_> {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    self.print(f, Prec::Term)
  }
}
