![Zenith](docs/title.png)

-----

[![build](https://github.com/bridgekat/zenith/actions/workflows/build.yml/badge.svg)](https://github.com/bridgekat/zenith/actions/workflows/build.yml)

This project is my personal attempt at making a theorem prover with an optimised interactive interface, intended for use by both brute-force search strategies and LLMs. It is based on a bare-bones type theory with only dependent functions (`Π` types), dependent pairs (`Σ` types), the `Unit` type, and two universes `Type : Kind`. All other types are to be expressed as postulates.

The `Σ` and `Unit` types are presented as "dependent tuples" which follow the usual rules of snoc-lists of nested `Σ`-types, and are implemented using contiguous arrays in the small kernel (\~400 LOC without I/O and errors) for fast random access to element values and types.

Example proof terms in the surface syntax:

- Some [`smalltt`](https://github.com/AndrasKovacs/smalltt) eval benchmarks: [`examples/tree_eval.zkt`](examples/tree_eval.zkt).
  - Type checking this term requires compiling with `cargo build --features type_in_type`.
- Linear-time environment lookup: [`examples/long_env_eval.zkt`](examples/long_env_eval.zkt).
  - Should be acceptable if deeply nested lambdas/lets are uncommon, or can be uncurried using dependent tuples.
  - Linked frames with greedy extend did not seem to worth the complication. Even if lookup path lengths are reduced to nearly 1, the additional constant overhead seemed more significant, except on intentionally crafted benchmarks like this one.
- Constant-time dependent tuple lookup: [`examples/long_tuple_eval.zkt`](examples/long_tuple_eval.zkt).
- Some basic first-order logic theorems: [`examples/first_order_logic.zt`](examples/first_order_logic.zt).

## Design

- My [final year project report](docs/design_report.pdf). I am still working on the problems mentioned in the final section.

## Progress

- [x] Implement a [core language](src/kernel/term.rs) with `Π`, `Σ` and `Unit` types.
- [x] Implement a [surface language](src/ir/term.rs) with holes.
- [x] Parsing and printing surface terms.
- [ ] The tableau system.
- [ ] The connection system.
- [ ] Some tooling?

For the sake of simplicity, **computation of (co)inductive types is not included**. The first development stage will not focus on any programming language stuff.
