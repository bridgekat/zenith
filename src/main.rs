#![feature(dropck_eyepatch)]

pub mod core;
pub mod elab;

use std::io::Write;

use core::{Arena, Stack, Term};

/// # Examples
///
/// - `[A : Type] -> [a : A] -> A`
/// - `([A] => [a] => a) : [A : Type] -> [a : A] -> A`
/// - `([Nat] => [add] => [a] => [add_self := ([x] => add x x) : [x: Nat] -> Nat] add_self a) :
///   [Nat: Type] -> [add: [a: Nat] -> [b: Nat] -> Nat] -> [a: Nat] -> Nat`
/// - `[Prop: Type] *
///   [Prf: [p: Prop] -> Type] *
///   [and: [p: Prop] -> [q: Prop] -> Prop] *
///   [and_intro: [p: Prop] -> [q: Prop] -> [hp: Prf p] -> [hq: Prf q] -> Prf (and p q)] *
///   [and_left: [p: Prop] -> [q: Prop] -> [h : Prf (and p q)] -> Prf p] *
///   [and_right: [p: Prop] -> [q: Prop] -> [h : Prf (and p q)] -> Prf q] *
///   Unit`
fn main() -> std::io::Result<()> {
  let prompt = "> ";
  loop {
    let ar = Arena::new();
    let mut line = String::new();
    print!("{prompt}");
    std::io::stdout().flush()?;
    std::io::stdin().read_line(&mut line)?;
    let trimmed = line.trim_end();
    let spans = match Term::lex(trimmed) {
      Ok(t) => t,
      Err(e) => {
        let (start, end) = e.position(trimmed.len());
        let end = end.max(start + 1);
        let indicator = " ".repeat(prompt.len() + start) + &"~".repeat(end - start);
        println!("{indicator}");
        println!("Error: {e}");
        continue;
      }
    };
    let term = match Term::parse(spans, &ar) {
      Ok(t) => t,
      Err(e) => {
        let (start, end) = e.position(trimmed.len());
        let end = end.max(start + 1);
        let indicator = " ".repeat(prompt.len() + start) + &"~".repeat(end - start);
        println!("{indicator}");
        println!("Error: {e}");
        continue;
      }
    };
    match term.infer(&Stack::new(), &Stack::new(), &ar) {
      Ok(t) => match t.quote(0, &ar) {
        Ok(t) => println!(": {t}"),
        Err(e) => println!("Error: {e}"),
      },
      Err(e) => println!("Error: {e}"),
    };
    match term.eval(&Stack::new(), &ar) {
      Ok(t) => match t.quote(0, &ar) {
        Ok(t) => println!("= {t}"),
        Err(e) => println!("Error: {e}"),
      },
      Err(e) => println!("Error: {e}"),
    };
    println!();
  }
}
