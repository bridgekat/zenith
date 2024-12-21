#![feature(dropck_eyepatch)]

pub mod core;
pub mod elab;

use std::io::Write;

use core::{Arena, Stack, Term};

/// # Examples
///
/// - `([A] ↦ [a] ↦ a) : [A : Type] → [a : A] → A`
/// - `([P] ↦ [Q] ↦ [h] ↦ [hq ≔ Fst (Snd h)], [hp ≔ Fst h], [])
///   : [P : Type] → [Q : Type] → [h : [hp : P] × [hq : Q] × Unit] → [hq : Q] × [hp : P] × Unit`
/// - `[Prop : Type] ×
///   [⊢ : [p : Prop] → Type] ×
///   [∧ : [p : Prop] → [q : Prop] → Prop] ×
///   [∧intro : [p : Prop] → [q : Prop] → [hp : ⊢ p] → [hq : ⊢ q] → ⊢ (∧ p q)] ×
///   [∧left : [p : Prop] → [q : Prop] → [h : ⊢ (∧ p q)] → ⊢ p] ×
///   [∧right : [p : Prop] → [q : Prop] → [h : ⊢ (∧ p q)] → ⊢ q] ×
///   Unit`
/// - `[I ≔ [x] ↦ x]
///   [K ≔ [x] ↦ [y] ↦ x]
///   [S ≔ [x] ↦ [y] ↦ [z] ↦ x z (y z)]
///   [Y ≔ [f] ↦ ([x] ↦ f ([_] ↦ x x)) ([x] ↦ f ([_] ↦ x x))]
///   [true ≔ [x] ↦ [y] ↦ x]
///   [false ≔ [x] ↦ [y] ↦ y]
///   [if ≔ [b] ↦ [t] ↦ [f] ↦ b t f []]
///   [succ ≔ [n] ↦ [x] ↦ [y] ↦ y n]
///   [pred ≔ [n] ↦ n K I]
///   [is_zero ≔ [n] ↦ if n ([_] ↦ true) ([_] ↦ [p] ↦ false)]
///   [0 ≔ K]
///   [1 ≔ succ 0]
///   [2 ≔ succ 1]
///   [3 ≔ succ 2]
///   [4 ≔ succ 3]
///   [5 ≔ succ 4]
///   [+ ≔ Y [self] ↦ [n] ↦ [m] ↦ if (is_zero n) ([_] ↦ m) ([_] ↦ succ (self [] (pred n) m))]
///   (+ 2 3)` *(not typable)*
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
        println!();
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
        println!();
        continue;
      }
    };
    match term.eval(&Stack::new(), &ar) {
      Ok(t) => match t.quote(0, &ar) {
        Ok(t) => println!("≡ {t}"),
        Err(e) => println!("Error: {e}"),
      },
      Err(e) => println!("Error: {e}"),
    };
    match term.infer(&Stack::new(), &Stack::new(), &ar) {
      Ok(t) => match t.quote(0, &ar) {
        Ok(t) => println!(": {t}"),
        Err(e) => println!("Error: {e}"),
      },
      Err(e) => println!("Error: {e}"),
    };
    println!();
  }
}
