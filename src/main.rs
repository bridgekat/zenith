pub mod core;
pub mod elab;

use bumpalo::Bump;

use core::term::{Context, Sort, Term::*};

fn main() {
  let pool = Bump::new();
  let id_sig = Pi(pool.alloc(Univ(Sort(1))), pool.alloc(Pi(pool.alloc(Var(0)), pool.alloc(Var(1)))));
  let id = Lam(pool.alloc(Univ(Sort(1))), pool.alloc(Lam(pool.alloc(Var(0)), pool.alloc(Var(0)))));

  print!("{id_sig} : ");
  match id_sig.assign_type(&mut Context::new(), &pool) {
    Ok(t) => println!("{t}"),
    Err(e) => println!("{e}"),
  }

  print!("{id} : ");
  match id.assign_type(&mut Context::new(), &pool) {
    Ok(t) => println!("{t}"),
    Err(e) => println!("{e}"),
  }

  match id.check_type(id_sig, &mut Context::new(), &pool) {
    Ok(()) => println!("Ok"),
    Err(e) => println!("{e}"),
  }
}
