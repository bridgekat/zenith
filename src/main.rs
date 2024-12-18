pub mod core;
pub mod elab;

use typed_arena::Arena;

use core::{Ctx, Env, Term, Univ};

fn main() {
  let terms = Arena::new();
  let vals = Arena::new();
  let ty = terms.alloc(Term::Pi(
    terms.alloc(Term::Univ(Univ(0))),
    terms.alloc(Term::Pi(terms.alloc(Term::Var(0)), terms.alloc(Term::Var(1)))),
  ));
  let tm = terms.alloc(Term::Ann(terms.alloc(Term::Fun(terms.alloc(Term::Fun(terms.alloc(Term::Var(0)))))), ty));

  print!("{ty} : ");
  match ty.infer(&Ctx::new(), &Env::new(), &vals) {
    Ok(t) => println!("{}", t.quote(0, &terms, &vals).unwrap()),
    Err(e) => println!("{e}"),
  };

  print!("{tm} : ");
  match tm.infer(&Ctx::new(), &Env::new(), &vals) {
    Ok(t) => println!("{}", t.quote(0, &terms, &vals).unwrap()),
    Err(e) => println!("{e}"),
  };
}
