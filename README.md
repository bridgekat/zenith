![Zenith](docs/title.png)

-----

[![build](https://github.com/bridgekat/zenith/actions/workflows/build.yml/badge.svg)](https://github.com/bridgekat/zenith/actions/workflows/build.yml)

This project is my personal attempt at making a theorem prover with an optimised interactive UI logic. It is based on a bare-bones type theory with only dependent functions (`Π` types), dependent pairs (`Σ` types), the `Unit` type, and two universes `Type : Kind`. All other types are to be expressed as postulates.

The `Σ` and `Unit` types are presented as "dependent tuples" which follow the usual rules of snoc-lists of nested `Σ`-types, and are implemented using contiguous arrays in the small kernel (\~400 LOC without I/O and errors) for fast random access to element values and types.

Example proof terms in the surface syntax:

- Some [`smalltt`](https://github.com/AndrasKovacs/smalltt) eval benchmarks: [`examples/tree_eval.zkt`](examples/tree_eval.zkt).
  - Type checking this term requires compiling with `cargo build --features type_in_type`.
- Linear-time environment lookup: [`examples/long_env_eval.zkt`](examples/long_env_eval.zkt).
  - Should be acceptable if deeply nested lambdas/lets are uncommon, or can be uncurried using dependent tuples.
  - Linked frames with greedy extend did not seem to worth the complication. Even if lookup path lengths are reduced to nearly 1, the additional constant overhead seemed more significant, except on intentionally crafted benchmarks like this one.
- Constant-time dependent tuple lookup: [`examples/long_tuple_eval.zkt`](examples/long_tuple_eval.zkt).
- Some basic first-order logic theorems: [`examples/first_order_logic.zt`](examples/first_order_logic.zt).

## Scope

- [x] Implement a [core language](src/kernel/term.rs) with `Π`, `Σ` and `Unit` types;
- [x] Implement a [surface language](src/ir/term.rs) with holes;
- [x] Parsing and printing surface terms;
- [x] The "elaborator" which turns a surface term into an acceptable proof state (but does not attempt unification);
- [ ] The transition system:
  - [ ] Specify the proof states (term with holes + typing constraints on holes + unification constraints on holes);
  - [ ] Specify the proof steps (backward chaining + forward chaining + Huet-simplify + Huet-match);
  - [ ] Checking validity of steps;
  - [ ] Listing valid steps;
  - [ ] Consider possible optimisations.
- [ ] Shortcuts;
- [ ] Some tooling?

For the sake of simplicity, **computation of (co)inductive types is not included**. The first development stage will not focus on any programming language stuff.

## References for next steps (non-exhaustive)

- [`elaboration-zoo`](https://github.com/AndrasKovacs/elaboration-zoo/tree/master/03-holes) (introduction to holes)
- [Dependently Typed Functional Programs and their Proofs](http://strictlypositive.org/thesis.pdf) (scoped holes with restricted computation)
- [An Efficient Unification Algorithm](http://www.nsl.com/misc/papers/martelli-montanari.pdf) (Robinson's system, Martelli-Montanari variable ordering)
- [Higher-order Unification](https://www21.in.tum.de/teaching/sar/SS20/5.pdf) (Huet's system)
- [Extensions and Applications of Higher-order Unification](http://conal.net/papers/elliott90.pdf) (Huet's system with typing constraints)
- [Aesop: White-Box Best-First Proof Search for Lean](https://people.compute.dtu.dk/ahfrom/aesop-camera-ready.pdf)
- [Three Tactic Theorem Proving](https://typeset.io/pdf/three-tactic-theorem-proving-gdzb8ziz3u.pdf)
- [Connections: Markov Decision Processes for Classical, Intuitionistic, and Modal Connection Calculi](https://api.repository.cam.ac.uk/server/api/core/bitstreams/1d51ebf4-6d8a-418f-9247-8cf18bc22751/content)
- [Experiments with Discrimination-Tree Indexing and Path Indexing for Term Retrieval](https://link-springer-com.iclibezp1.cc.ic.ac.uk/content/pdf/10.1007/BF00245458.pdf)
