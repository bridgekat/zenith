#![feature(dropck_eyepatch)]

pub mod core;
pub mod elab;

use core::{Arena, Stack, Term, Univ};

fn main() {
  let ar = Arena::new();
  let ty =
    ar.term(Term::Pi(ar.term(Term::Univ(Univ(0))), ar.term(Term::Pi(ar.term(Term::Var(0)), ar.term(Term::Var(1))))));
  let tm = ar.term(Term::Ann(ar.term(Term::Fun(ar.term(Term::Fun(ar.term(Term::Var(0)))))), ty));

  print!("{ty} : ");
  match ty.infer(&Stack::new(), &Stack::new(), &ar) {
    Ok(t) => println!("{}", t.quote(0, &ar).unwrap()),
    Err(e) => println!("{e}"),
  };

  print!("{tm} : ");
  match tm.infer(&Stack::new(), &Stack::new(), &ar) {
    Ok(t) => println!("{}", t.quote(0, &ar).unwrap()),
    Err(e) => println!("{e}"),
  };
}
