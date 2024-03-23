# Zenith theorem prover (planned)

This is my personal attempt at making a theorem prover centred around the classical foundation of ZFC, but which also uses dependent types as an abstraction mechanism to facilitate the organisation of mathematical theories.

If possible, this will be made compatible with other foundations as well.

## Scope

Goals:

- Implement a core language based on the [calculus of constructions](https://en.wikipedia.org/wiki/Calculus_of_constructions);
- Implement an elaborator with type inference and support for typeclasses;
- Inject primitive types to make a programming language;
- Formalise and use categories as the organising principle of mathematics;
- Keep compatibility with different axioms and foundations;
- Support interaction with special-purpose automated theorem provers (e.g. tableaux for first-order logic, SMT for arithmetic, etc).

Non-goals:

- Implement (co)inductive types in the core language;
- Focus on constructive mathematics;
- Focus on the univalence axiom and the interpretation of propositional equalities as homotopies.

For the sake of simplicity, **computation of (co)inductive types is excluded from the core language**. This should be recovered by assuming additional propositional equalities and writing scripts for term normalisation. *(I disliked having to distinguish "definitional equality" from "propositional equality" in modern theorem provers...)*
