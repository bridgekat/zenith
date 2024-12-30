use std::fmt::Formatter;

use crate::intermediate::term::Term;

/// Variable bindings.
#[derive(Debug, Clone)]
enum Binding {
  Named(String),
  Tuple(Vec<String>),
}

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
        match v {
          0 => write!(f, "Type")?,
          1 => write!(f, "Kind")?,
          _ => write!(f, "<unsupported universe level>")?,
        };
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
      Term::Ann(x, t, b) => {
        left_paren(f, Prec::Term, prec)?;
        x.print(f, count, vars, Prec::Body)?;
        match b {
          false => write!(f, " : ")?,
          true => write!(f, " :: ")?,
        }
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

impl std::fmt::Display for Term<'_> {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    self.print(f, &mut 0, &mut Vec::new(), Prec::Term)
  }
}
