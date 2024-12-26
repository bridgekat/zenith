# Zenith theorem prover

![Zenith](docs/title.png)

This project is my personal attempt at making a theorem prover with an optimised interactive UI logic. It is based on a bare-bones type theory with only dependent functions (`Π`-types), dependent pairs (`Σ`-types), the `Unit` type, and two universes `Type : Kind`. All other types are to be expressed as postulates.

The `Σ` and `Unit` types are presented as "dependent tuples" which follow the usual rules of snoc-lists of nested `Σ`-types, and are implemented using contiguous arrays in the small kernel (\~500 LOC without I/O and errors) for fast random access to element values and types.

Example proof terms in the core syntax:

- Some basic first-order logic theorems: [`examples/first_order_logic.term`](examples/first_order_logic.term).
- Some [`smalltt`](https://github.com/AndrasKovacs/smalltt) eval benchmarks: [`examples/tree_eval.term`](examples/tree_eval.term).
  - Type checking this term requires compiling with `cargo build --features type_in_type`.
- Linear-time environment lookup: [`examples/long_env_eval.term`](examples/long_env_eval.term).
  - Should be acceptable if deeply nested lambdas/lets are uncommon, or can be uncurried using dependent tuples.
  - Linked frames with greedy extend did not seem to worth the complication. Even if lookup path lengths are reduced to nearly 1, the additional constant overhead seemed more significant, except on intentionally crafted benchmarks like this one.
- Constant-time dependent tuple lookup: [`examples/long_tuple_eval.term`](examples/long_tuple_eval.term).

## Scope

Goals:

- Implement a [core language](src/core/term.rs) based on the [calculus of constructions](https://en.wikipedia.org/wiki/Calculus_of_constructions);
- Implement an elaborator with type inference and support for typeclasses;
- Formalise basic mathematical concepts;
- Implement an optimised tactic mode.

For the sake of simplicity, **computation of (co)inductive types is excluded from the core language**. The first development stage will not focus on any programming language stuff.
