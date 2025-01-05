use zenith::arena::Arena;
use zenith::ir::{Stack, Term, TypeError};

fn check<'b>(x: &str, t: &str, ctx: &Stack<'_, 'b>, env: &Stack<'_, 'b>, ar: &'b Arena) {
  let t = Term::parse(Term::lex(t.chars()).unwrap().into_iter(), ar).unwrap();
  let (t, tt) = t.infer(ctx, env, ar).unwrap();
  tt.as_univ(|tt| TypeError::type_expected(&t, tt, ctx, env, ar)).unwrap();
  let t = t.eval(env, ar).unwrap();
  let x = Term::parse(Term::lex(x.chars()).unwrap().into_iter(), ar).unwrap();
  let _ = x.check(t, ctx, env, ar).unwrap();
}

fn check_and_eval<'b>(x: &str, y: &str, t: &str, ctx: &Stack<'_, 'b>, env: &Stack<'_, 'b>, ar: &'b Arena) {
  let t = Term::parse(Term::lex(t.chars()).unwrap().into_iter(), ar).unwrap();
  let (t, tt) = t.infer(ctx, env, ar).unwrap();
  tt.as_univ(|tt| TypeError::type_expected(&t, tt, ctx, env, ar)).unwrap();
  let t = t.eval(env, ar).unwrap();
  let x = Term::parse(Term::lex(x.chars()).unwrap().into_iter(), ar).unwrap();
  let x = x.check(t, ctx, env, ar).unwrap();
  let x = x.eval(env, ar).unwrap();
  let y = Term::parse(Term::lex(y.chars()).unwrap().into_iter(), ar).unwrap();
  let y = y.check(t, ctx, env, ar).unwrap();
  let y = y.eval(env, ar).unwrap();
  assert!(x.conv(&y, ctx.len(), ar).unwrap());
}

#[test]
fn test_check_and_eval_id() {
  let ar = Arena::new();
  check_and_eval(
    r"[id ≔ [X, x] ↦ x : [X : Type, x : X] → X] [A] ↦ id ([a : A] → A) (id A)",
    r"[X, x] ↦ x",
    r"[A : Type, a : A] → A",
    &Stack::new(&ar),
    &Stack::new(&ar),
    &ar,
  );
}

#[test]
fn test_check_and_eval_tuple() {
  let ar = Arena::new();
  check_and_eval(
    r"[P, Q, h] ↦ {hq ≔ h^0, hp ≔ h^1, hr := h^0}",
    r"[P, Q, h] ↦ {hq ≔ h^0, hp ≔ h^1, hr := hq}",
    r"[P : Type, Q : Type, h : {hp : P, hq : Q}] → {hq : Q, hp : P, hr : Q}",
    &Stack::new(&ar),
    &Stack::new(&ar),
    &ar,
  );
}

#[test]
fn test_check_and_eval_church_naturals() {
  let ar = Arena::new();
  check_and_eval(
    r"
    [
      ℕ ≔ [A : Type, s : [a : A] → A, z : A] → A,
      add ≔ [n, m, A, s, z] ↦ n A s (m A s z) : [n : ℕ, m : ℕ] → ℕ,
      mul ≔ [n, m, A, s, z] ↦ n A (m A s) z : [n : ℕ, m : ℕ] → ℕ,
      5 ≔ [A, s, z] ↦ s (s (s (s (s z)))) : ℕ,
      10 ≔ add 5 5,
      50 ≔ mul 10 5
    ]
      50
    ",
    r"[A, s, z] ↦
      (s (s (s (s (s (s (s (s (s (s
      (s (s (s (s (s (s (s (s (s (s
      (s (s (s (s (s (s (s (s (s (s
      (s (s (s (s (s (s (s (s (s (s
      (s (s (s (s (s (s (s (s (s (s
      z
      ))))))))))
      ))))))))))
      ))))))))))
      ))))))))))
      ))))))))))
    ",
    r"[A : Type, s : [a : A] → A, z : A] → A",
    &Stack::new(&ar),
    &Stack::new(&ar),
    &ar,
  );
}

#[test]
fn test_check_first_order_logic_de_morgan_proof() {
  let ar = Arena::new();
  check(
    r"
    [
      Prop, ⊢, ⊥, ¬, ∧, ∨, ⇒, ⇔, X, ∀, ∃,
      ⊥elim, ¬intro, contra, ¬elim, ∧intro, ∧left, ∧right, ∨inl, ∨inr, ∨elim,
      ⇒intro, ⇒elim, ⇔intro, ⇔left, ⇔right, ∀intro, ∀elim, ∃intro, ∃elim
    ]
      ↦
    {
      not-or-iff-and-not ≔
        ([p, q] ↦ ⇔intro (¬ (∨ p q)) (∧ (¬ p) (¬ q))
          ([h] ↦ ∧intro (¬ p) (¬ q)
            (¬intro p ([hp] ↦ ¬elim (∨ p q) h (∨inl p q hp)))
            (¬intro q ([hq] ↦ ¬elim (∨ p q) h (∨inr p q hq))))
          ([h] ↦ ¬intro (∨ p q)
            ([hpq] ↦ ∨elim p q ⊥ hpq
              ([hp] ↦ ¬elim p (∧left (¬ p) (¬ q) h) hp)
              ([hq] ↦ ¬elim q (∧right (¬ p) (¬ q) h) hq)))),

      not-exists-iff-forall-not ≔
        ([p] ↦ ⇔intro (¬ (∃ ([x] ↦ p x))) (∀ ([x] ↦ ¬ (p x)))
          ([h] ↦ ∀intro ([x] ↦ ¬ (p x))
            ([x] ↦ ¬intro (p x)
              ([hp] ↦ ¬elim (∃ ([x] ↦ p x)) h (∃intro ([x] ↦ p x) x hp))))
          ([h] ↦ ¬intro (∃ ([x] ↦ p x))
            ([hp] ↦ ∃elim ([x] ↦ p x) ⊥ hp
              ([x, hx] ↦ ¬elim (p x) (∀elim ([x] ↦ ¬ (p x)) h x) hx))))
    }
    ",
    r"
    [
      Prop : Type,
      ⊢ : [_ : Prop] → Type,
      ⊥ : Prop,
      ¬ : [_ : Prop] → Prop,
      ∧ : [_ : Prop, _ : Prop] → Prop,
      ∨ : [_ : Prop, _ : Prop] → Prop,
      ⇒ : [_ : Prop, _ : Prop] → Prop,
      ⇔ : [_ : Prop, _ : Prop] → Prop,
      X : Type,
      ∀ : [_ : [_ : X] → Prop] → Prop,
      ∃ : [_ : [_ : X] → Prop] → Prop,
      ⊥elim : [c : Prop, _ : ⊢ ⊥] → ⊢ c,
      ¬intro : [p : Prop, _ : [_ : ⊢ p] → ⊢ ⊥] → ⊢ (¬ p),
      contra : [p : Prop, _ : [_ : ⊢ (¬ p)] → ⊢ ⊥] → ⊢ p,
      ¬elim : [p : Prop, _ : ⊢ (¬ p), _ : ⊢ p] → ⊢ ⊥,
      ∧intro : [p : Prop, q : Prop, _ : ⊢ p, _ : ⊢ q] → ⊢ (∧ p q),
      ∧left : [p : Prop, q : Prop, _ : ⊢ (∧ p q)] → ⊢ p,
      ∧right : [p : Prop, q : Prop, _ : ⊢ (∧ p q)] → ⊢ q,
      ∨inl : [p : Prop, q : Prop, _ : ⊢ p] → ⊢ (∨ p q),
      ∨inr : [p : Prop, q : Prop, _ : ⊢ q] → ⊢ (∨ p q),
      ∨elim : [p : Prop, q : Prop, c : Prop, _ : ⊢ (∨ p q), _ : [_ : ⊢ p] → ⊢ c, _ : [_ : ⊢ q] → ⊢ c] → ⊢ c,
      ⇒intro : [p : Prop, q : Prop, _ : [_ : ⊢ p] → ⊢ q] → ⊢ (⇒ p q),
      ⇒elim : [p : Prop, q : Prop, _ : ⊢ (⇒ p q), _ : ⊢ p] → ⊢ q,
      ⇔intro : [p : Prop, q : Prop, _ : [_ : ⊢ p] → ⊢ q, _ : [_ : ⊢ q] → ⊢ p] → ⊢ (⇔ p q),
      ⇔left : [p : Prop, q : Prop, _ : ⊢ (⇔ p q), _ : ⊢ q] → ⊢ p,
      ⇔right : [p : Prop, q : Prop, _ : ⊢ (⇔ p q), _ : ⊢ p] → ⊢ q,
      ∀intro : [p : [_ : X] → Prop, _ : [x : X] → ⊢ (p x)] → ⊢ (∀ p),
      ∀elim : [p : [_ : X] → Prop, _ : ⊢ (∀ p), x : X] → ⊢ (p x),
      ∃intro : [p : [_ : X] → Prop, x : X, _ : ⊢ (p x)] → ⊢ (∃ p),
      ∃elim : [p : [_ : X] → Prop, c : Prop, _ : ⊢ (∃ p), _ : [x : X, _ : ⊢ (p x)] → ⊢ c] → ⊢ c
    ]
      →
    {
      not-or-iff-and-not : [p : Prop, q : Prop] → ⊢ (⇔ (¬ (∨ p q)) (∧ (¬ p) (¬ q))),
      not-exists-iff-forall-not : [p : [_ : X] → Prop] → ⊢ (⇔ (¬ (∃ ([x] ↦ p x))) (∀ ([x] ↦ ¬ (p x))))
    }
    ",
    &Stack::new(&ar),
    &Stack::new(&ar),
    &ar,
  )
}
