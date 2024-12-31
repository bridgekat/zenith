use std::marker::PhantomData;

use super::*;
use crate::arena::Arena;
use crate::term::{Core, Decoration, Term};

#[derive(Debug, Clone, Copy)]
pub enum Var<'a> {
  Ix(usize),
  Name(&'a str, usize, usize),
}

#[derive(Debug, Clone, Copy)]
pub struct Named<'a> {
  _marker: PhantomData<&'a ()>,
}

impl<'a> Decoration for Named<'a> {
  type Var = Var<'a>;
}

impl<'a> Term<'a, Named<'a>> {
  pub fn resolve(
    &'a self,
    vars: &mut Vec<(&'a str, &'a Term<'a, Core>)>,
    ar: &'a Arena,
  ) -> Result<&'a Term<'a, Core>, ParseError> {
    match self {
      Term::Univ(u) => Ok(ar.term(Term::Univ(*u))),
      Term::Var(var) => match var {
        Var::Ix(ix) => Ok(ar.term(Term::Var(*ix))),
        Var::Name(name, start, end) => todo!(),
      },
      Term::Ann(x, t, b) => Ok(ar.term(Term::Ann(x.resolve(vars, ar)?, t.resolve(vars, ar)?, *b))),
      Term::Let(i, v, x) => Ok(ar.term(Term::Let(*i, v.resolve(vars, ar)?, x.resolve(vars, ar)?))),
      Term::Pi(i, t, u) => Ok(ar.term(Term::Pi(*i, t.resolve(vars, ar)?, u.resolve(vars, ar)?))),
      Term::Fun(i, b) => Ok(ar.term(Term::Fun(*i, b.resolve(vars, ar)?))),
      Term::App(f, x, b) => Ok(ar.term(Term::App(f.resolve(vars, ar)?, x.resolve(vars, ar)?, *b))),
      Term::Sig(i, t, u) => Ok(ar.term(Term::Sig(*i, t.resolve(vars, ar)?, u.resolve(vars, ar)?))),
      Term::Tup(i, a, b) => Ok(ar.term(Term::Tup(*i, a.resolve(vars, ar)?, b.resolve(vars, ar)?))),
      Term::Init(n, x) => Ok(ar.term(Term::Init(*n, x.resolve(vars, ar)?))),
      Term::Last(x) => Ok(ar.term(Term::Last(x.resolve(vars, ar)?))),
      Term::Unit => Ok(ar.term(Term::Unit)),
      Term::Star => Ok(ar.term(Term::Star)),
    }
  }
}
