
#ai none // Proof terms only
any x, y, z {
  assume x = y name h1, y = z name h2 {
    => x = z name h proof eq.trans h1 h2; // Use `proof` to provide proof terms
    #ls // h : x = z
  }
  #ls // h : x = y -> y = z -> x = z
}
#ls // h : forall x, y, z, x = y -> y = z -> x = z

#ai search_simple // Analytic tableaux & simple unifier activated
any x, y, z {
  assume x = y, y = z {
    /*
    => x = z by eq.trans; // Use `by` to provide hints to the AI
    => x = z by "transitivity of equality"; // Use of complex names is also supported (fuzzy matching, and you can search by this)
    */
  }
}

#ai nn_alpha_turnstile_zero // Neural networks activated! If you take small steps, there is no need to explicitly state the rules.
any x, y, z {
  assume x = y, y = z {
    => x = z;
  }
}

// One might as well use metavariables...
anypred r/2 {
  // Now you have a formula metavariable (predicate) r with arity 2 (or more precisely, at least 2)...
  assume (forall x,       r x x),
         (forall x, y,    r x y -> r y x -> x = y),
         (forall x, y, z, r x y -> r y z -> r x z) {
    // Assume r is a partial order...
    any x, y, z assume r x y, r y z, r z x {
      => x = y;
      => x = z;
      => y = z;
    }
  }
}
#ls // The first one is ? : forallpred r/2, (...) -> (...) -> (...) -> forall x, y, z, r x y -> r y z -> r z x -> x = y
// You can now substitute in any formula in the place of r! (Use forallpred.e or forallfunc.e, just like forall.e)
// This is actually a "second-order" forall.e...

// In ApiMu, only limited second-order reasoning is supported (I guess this removes some burden from the AI (and me)).
// Namely, every `forallpred` and `forallfunc` must appear at the beginning of a formula.
// Also, there is no second-order `exists`...
any x {
  assume x = x {
    anyfunc f/2, anypred p/1, any a, b => p (f a b) <-> p (f a b);
    #ls // ? : forallfunc f/2, forallpred p/1, forall a, b, p (f a b) <-> p (f a b)
  }
  #ls // (the above ? vanishes)

  anyfunc f/2, anypred p/1, any a, b => p (f a b) <-> p (f a b);
  #ls // ? : forallfunc f/2, forallpred p/1, forall a, b, p (f a b) <-> p (f a b)
}
#ls // ? : forallfunc x/0, f/2, forallpred p/1, forall a, b, p (f a b) <-> p (f a b)

assume (forallpred p/0, p) name h {
  => false by forallpred.e h false;
  => false by h false; // (Alternatively) `forallpred.e` can be omitted, similar to `forall.e` and `imp.e` (just like in Lean)
}
#ls // The above declaration does not escape the scope and produce ((forallpred p/0, p) -> false)!

// By design, formulas with `forallpred` and `forallfunc` should actually be understood as first-order "formula schemas", and they are useful only in two cases:
// 1. Declaring primitive notions (i.e. "signature of the language")
// 2. Expressing axiom schemas (schemes, schemata)
// 3. Deriving generic results about formulas and terms
// (You can nonetheless regard them as "formulas with second-order variables", as this only affects the metatheory which we don't need to care...)
anypred p/0 {
  assume not (p or not p) {
    assume p { => p or not p; => false; } => not p;
    => p or not p; => false;
  }
  => p or not p by raa;
}
=> forallpred p/0, p or not p name lem;

any x, y, => x = y or not x = y by lem (x = y);
=> forall x, y, x = y or not x = y;

// Metavariables can be substituted for formulas/terms that contain metavariables, in a similar mannar as in Metamath...
// (We don't have "disjointness constraints", as we use de Brujin indices and every substitution will be made proper!)
anypred q/2, any x, y {
  => q x y or not q x y by lem (q x y);
}
=> forallpred q/2, forall x, y, q x y or not q x y name random_lemma;


// Taking the "schema" perspective, the above metavariable rules are a conservative extension of first-order logic with equality.
// "Extension by definitions" is another kind of conservative extension, which allows us to "define" a function or predicate...
any x, y {
  def phi :<-> x = y and y = x name phi_def;
  #ls // phi_def : phi <-> (x = y and y = x)
}
#ls // phi_def : forall x, y, phi x y <-> (x = y and y = x)
undef phi;
#ls // (phi and phi_def vanish)

// Alternatively...
any x, y def phi :<-> x = y and y = x name phi_def;
#ls // phi_def : (forall x, y, phi x y <-> (x = y and y = x))

// Combining `def` and `assume` gives partial functions!
// (Assuming we have defined a function with infix notation `+`...)
any x, y assume x = y {
  def f := x + y name f_def;
  #ls // f_def : f = x + y
}
#ls // f_def : forall x, y, x = y -> f x y = x + y

// Defined predicates and functions can be used to substitute metavariables too (syntactic sugar)
=> forall x, y, phi x y or not phi x y by random_lemma phi;

// One could do "inline definitions" using something similar to the "lambda notation"!
// This saves some typing by avoiding defining and undefining named functions / predicates. They are not necessary to the theory.
// Note that the `a` `b` here are all individual variables.
=> forall x, y, x + y = 2 or not x + y = 2 by random_lemma (a b | a + b = 2);




/*
// Summary
// Context: contains four types of things:
Individual variables        ι
Function variables          ι → ... → ι
Predicate variables         ι → ... → Prop
Assumptions                 * : Prop
Theorems                    * : Prop            // (Can contain things generated by the inference engine)
// Context-changing rules (and their targets):
any x { ... }               forall x, ...
anyfunc f/n { ... }         forallfunc f/n, ... // (Not commonly used)
anypred p/n { ... }         forallpred p/n, ... // (Not commonly used)
assume (...) { ... }        ... -> ...
// Non-context-changing rules (and their targets):
and.i and.l and.r           and        ∧
or.l or.r or.e              or         ∨
implies.e                   implies    →
not.i not.e                 not        ¬
iff.i iff.l iff.r           iff        ↔
eq.i eq.e eq.symm eq.trans  eq         =
forall.e                    forall     ∀
exists.i exists.e           exists     ∃
unique.i unique.l unique.r  unique     ∃!
forallfunc.e                forallfunc ∀#       // (Only used on a few instances)
forallpred.e                forallpred ∀$       // (Only used on a few instances)
true.i                      true       ⊤
false.e raa                 false      ⊥
// Extension by definitions
def := :: :<-> idef :: undef
// (The above is ALL of the logic. There will be NO further extensions. Hopefully this makes an AI easier to build...?)

// Auxiliary keywords (some are used to guide AI, some are used to guide human readers)
=> by name namespace private public
*/

