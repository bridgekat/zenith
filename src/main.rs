pub mod core;

use typed_arena::Arena;

use core::term::{Sort::*, Term::*};

fn main() {
  let pool = Arena::new();

  let id_sig = pool.alloc(Pi(pool.alloc(Sort(Type)), pool.alloc(Pi(pool.alloc(Var(0)), pool.alloc(Var(1))))));
  println!("{id_sig}");
  match id_sig.infer_type(&mut Vec::new(), &pool) {
    Ok(t) => println!("{t}"),
    Err(e) => println!("{e}"),
  }

  let id = pool.alloc(Lam(pool.alloc(Sort(Type)), pool.alloc(Lam(pool.alloc(Var(0)), pool.alloc(Var(0))))));
  println!("{id}");
  match id.infer_type(&mut Vec::new(), &pool) {
    Ok(t) => println!("{t}"),
    Err(e) => println!("{e}"),
  }
}
