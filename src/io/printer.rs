use std::fmt::Formatter;

use crate::ir::{Decoration, Ix, Name, Term, Var};

/// Precedence levels.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Prec {
  Term,
  Body,
  Proj,
  Atom,
}

impl std::fmt::Display for Ix {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    write!(f, "@^{}", self.ix)
  }
}

impl std::fmt::Display for Name<'_> {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}", self.segments.join("::"))
  }
}

impl std::fmt::Display for Var<'_> {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    match self {
      Var::Ix(ix) => write!(f, "{}", ix),
      Var::Name(name) => write!(f, "{}", name),
    }
  }
}

impl<'b, T: Decoration<'b>> Term<'_, 'b, T>
where
  T::Var: std::fmt::Display,
{
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
      Term::Var(x) => {
        left_paren(f, Prec::Atom, prec)?;
        write!(f, "{}", x)?;
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
      Term::Sig(us) => {
        left_paren(f, Prec::Atom, prec)?;
        if us.is_empty() {
          write!(f, "Unit")?;
        } else {
          write!(f, "{{")?;
          for (j, (i, u)) in us.iter().enumerate() {
            if j != 0 {
              write!(f, ", ")?;
            }
            write!(f, "{} : ", present_name(i.name))?;
            u.print(f, Prec::Term)?;
          }
          write!(f, "}}")?;
        }
        right_paren(f, Prec::Atom, prec)?;
        Ok(())
      }
      Term::Tup(bs) => {
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
    }
  }
}

impl<'b, T: Decoration<'b>> std::fmt::Display for Term<'_, 'b, T>
where
  T::Var: std::fmt::Display,
{
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    self.print(f, Prec::Term)
  }
}
