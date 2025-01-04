#![feature(cell_update)]
#![warn(clippy::all)]

pub mod arena;
pub mod elab;
pub mod io;
pub mod ir;
pub mod kernel;

use std::io::Write;
use std::thread::Builder;

use arena::Arena;
use ir::{Stack, Term};

/// Converts `pos` to line and column numbers.
fn pos_to_line_col(pos: usize, lines: &[String]) -> (usize, usize) {
  let mut remaining = pos;
  for (i, line) in lines.iter().enumerate() {
    if remaining < line.chars().count() {
      return (i, remaining);
    }
    remaining -= line.chars().count();
  }
  match lines.last() {
    Some(line) => (lines.len() - 1, line.chars().count()),
    None => (0, 0),
  }
}

/// Prints a location indicator.
fn print_location_indicator(start: usize, end: usize, lines: &[String]) {
  let end = end.max(start);
  let (start_line, start_col) = pos_to_line_col(start, lines);
  let (end_line, end_col) = pos_to_line_col(end, lines);
  let line = lines.get(start_line).map_or("", |s| s.as_ref());
  if start_line == end_line {
    println!("|");
    println!("| {line}");
    println!("| {}{}", " ".repeat(start_col), "~".repeat((end_col - start_col).max(1)));
  } else {
    println!("|");
    println!("| {line}");
    println!("| {}{}", " ".repeat(start_col), "~".repeat(line.chars().count() - start_col));
  }
}

/// # Examples
///
/// ```term
/// [id ≔ [X, x] ↦ x : [X : Type, x : X] → X] [A] ↦ id ([a : A] → A) (id A) :
///   [A : Type, a : A] → A
/// ```
///
/// ```term
/// [P, Q, h] ↦ {hq ≔ h^0, hp ≔ h^1} :
///   [P : Type, Q : Type, h : {hp : P, hq : Q}] → {hq : Q, hp : P}
/// ```
///
/// ```term
/// {
///   Prop : Type,
///   ⊢ : [p : Prop] → Type,
///   ∧ : [p : Prop, q : Prop] → Prop,
///   ∧intro : [p : Prop, q : Prop, hp : ⊢ p, hq : ⊢ q] → ⊢ (∧ p q),
///   ∧left : [p : Prop, q : Prop, h : ⊢ (∧ p q)] → ⊢ p,
///   ∧right : [p : Prop, q : Prop, h : ⊢ (∧ p q)] → ⊢ q
/// }
/// ```
///
/// ```term
/// [
///   ℕ ≔ [A : Type, s : [a : A] → A, z : A] → A,
///   add ≔ [n, m, A, s, z] ↦ n A s (m A s z) : [n : ℕ, m : ℕ] → ℕ,
///   mul ≔ [n, m, A, s, z] ↦ n A (m A s) z : [n : ℕ, m : ℕ] → ℕ,
///   5 ≔ [A, s, z] ↦ s (s (s (s (s z)))) : ℕ,
///   10 ≔ add 5 5,
///   100 ≔ mul 10 10,
///   1000 ≔ mul 10 100
/// ]
///   1000
/// ```
///
/// ```term
/// [
///   I ≔ [x] ↦ x,
///   K ≔ [x, y] ↦ x,
///   S ≔ [x, y, z] ↦ x z (y z),
///   Y ≔ [f] ↦ ([x] ↦ f ([_] ↦ x x)) ([x] ↦ f ([_] ↦ x x)),
///   true ≔ [x, y] ↦ x,
///   false ≔ [x, y] ↦ y,
///   if ≔ [b, t, f] ↦ b t f {},
///   succ ≔ [n, x, y] ↦ y n,
///   pred ≔ [n] ↦ n K I,
///   is_zero ≔ [n] ↦ if n ([_] ↦ true) ([_, p] ↦ false),
///   0 ≔ K,
///   1 ≔ succ 0,
///   2 ≔ succ 1,
///   3 ≔ succ 2,
///   4 ≔ succ 3,
///   5 ≔ succ 4,
///   + ≔ Y ([self, n, m] ↦ if (is_zero n) ([_] ↦ m) ([_] ↦ succ (self {} (pred n) m)))
/// ]
///   + 2 3
/// ```
fn run_repl() -> std::io::Result<()> {
  let mut ar = Arena::new();
  loop {
    ar.reset();

    let mut lines = Vec::new();
    let mut line = String::new();

    print!("> ");
    std::io::stdout().flush()?;
    std::io::stdin().read_line(&mut line)?;
    line = line.trim_end_matches(|c| "\r\n".contains(c)).to_string();

    while !line.is_empty() {
      lines.push(line);
      line = String::new();

      print!("  ");
      std::io::stdout().flush()?;
      std::io::stdin().read_line(&mut line)?;
      line = line.trim_end_matches(|c| "\r\n".contains(c)).to_string();
    }

    let input = lines.join("");
    if input.is_empty() {
      continue;
    }

    let spans = match Term::lex(input.chars()) {
      Ok(t) => t,
      Err(e) => {
        let (start, end) = e.position(input.chars().count());
        println!("⨯ Error: {e}");
        print_location_indicator(start, end, &lines);
        println!();
        continue;
      }
    };

    let term = match Term::parse(spans.into_iter(), &ar) {
      Ok(t) => t,
      Err(e) => {
        let (start, end) = e.position(input.chars().count());
        println!("⨯ Error: {e}");
        print_location_indicator(start, end, &lines);
        println!();
        continue;
      }
    };

    match term.infer(&Stack::new(&ar), &Stack::new(&ar), &ar) {
      Ok((term, ty)) => match ty.quote(0, &ar) {
        Ok(ty) => match term.eval(&Stack::new(&ar), &ar) {
          Ok(term) => match term.quote(0, &ar) {
            Ok(t) => {
              println!("≡ {t}");
              println!(": {ty}");
            }
            Err(e) => println!("⨯ Error: {e}"),
          },
          Err(e) => println!("⨯ Error: {e}"),
        },
        Err(e) => println!("⨯ Error: {e}"),
      },
      Err(e) => println!("⨯ Error: {e}"),
    };

    println!();
    println!(
      "  Heap: {} terms, {} frames, {} values, {} closures",
      ar.term_count(),
      ar.frame_count(),
      ar.val_count(),
      ar.clos_count()
    );
    println!("  Stack: {} lookups, {} average lookup length", ar.lookup_count(), ar.average_link_count());
    println!();
  }
}

fn main() -> std::io::Result<()> {
  // Due to heavy use of recursion, stack size limit is set to 1 GB.
  Builder::new().stack_size(1024 * 1024 * 1024).spawn(run_repl)?.join().unwrap()?;
  Ok(())
}
