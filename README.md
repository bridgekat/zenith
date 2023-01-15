# ApiMu/ZFC

[![CMake build](https://github.com/bridgekat/apimu/actions/workflows/cmake-build.yml/badge.svg)](https://github.com/bridgekat/apimu/actions/workflows/cmake-build.yml)

I am too poor at mathematics so I have to make a "cheating engine" for myself!

Dependent type theory and [Lean](https://leanprover.github.io/) seem to be too difficult to learn... (Spent two months trying to make clear everything about its type theory, and then for example [it took me 40 lines to formalize a 5-line proof](https://github.com/bridgekat/lean-notes/blob/e8a9df5fff3feea2c5cc2d0112c101dd8d68f80c/src/2_analysis/1_the_real_and_complex_number_systems.lean#L448), even if I made use of automation tactics like `linarith`... And it seems hard to write new tactics...)

> [Metamath One](https://github.com/digama0/mm0/blob/master/mm0-hs/mm1.md) looks nice! I did not realize this earlier...
>
> (I am not aiming to make any serious ITP software! This is just a "toy" system for inexperienced users (and AI) to interact with, so I will just try to make the UI as intuitive as possible while keeping the background theory simple. It seems like first-order logic with equality (with natural deduction) + meta-variables (for axiom schemata) + extension by definitions are already enough for this...)
>
> (Update: just found out that using dependent type theory as a meta-logic actually *simplifies* code 😂. But I'm not going to add anything beyond basic Π-types and β-reduction for now. No intensional equality, no inductive types, the thing is there just to express first-order logic and second-order schema rules in a more manageable way...)


## Building (experimental)

Make sure a C++23 compiler (I'm using GCC 12.2) and CMake 3.15+ is available on your computer. In the root directory, run:

```sh
git submodule update --init --recursive
cmake -S . -B build
cmake --build build -j 4
```

If everything is fine, you can then find three executables (`testcore`, `testeval` and `testtest`) in the `build` directory.

The `testeval` is a REPL for a Scheme-like scripting language with reconfigurable syntax. The ability of changing syntax dynamically and freely comes from the [Earley method](https://en.wikipedia.org/wiki/Earley_parser) (see `src/parsing/parser.cpp`). It is currently very broken (e.g. simply gives up on handling ambiguous expressions without giving a proper error message) but still barely functional:

- Type `:quit` to exit
- Use `:{` to begin multi-line input, and end with a `:}` (must be in a separate line)
- Type `:load <filename>` to read and interpret a file statement-by-statement (equivalent to simply copy-pasting the whole file as multi-line input). You can find some examples in the `scripts` folder. 
  - `self.mu` contains equivalent definitions of the default syntax. Loading it will change the current syntax into default syntax, given that your current syntax correctly interprets its content (like the default syntax does. For example, this is the case when your current syntax is a superset of the default syntax).
  - `prelude.mu` contains definitions for the extended syntax, along with a few utility functions. Loading it will allow you to write Lean-3-looking code in parentheses (which can be freely mixed with original, Lisp-looking code in square brackets).
- Type `(add 2 2)` (`[add 2 2]` or `2 + 2;` for the extended syntax) to add up two numbers. (I will write a documentation for the language later...)

You may also try executing `testcore`, which runs some tests for the experimental tableau prover. Currently it is rather inefficient, and does not support equational or higher-order reasoning. Nevertheless, it already proves some first-order propositions that Lean's `finish` tactic, or even myself, cannot quickly prove (though I know that both are already considered weak and outdated, and winning them does not indicate anything special...)

The `testtest` does nothing.

*The `testserver` part is being rewritten... It won't compile for now.*

> The relevant one is `testserver`, which is a rudimentary LSP server that is supposed to parse `.mu` files.
>
> 1. Open the `vscode` directory in VSCode.
> 2. Press `Ctrl+Shift+B` and then `F5` (or probably directly pressing `F5` is enough) to start the Extension Development Host.
> 3. Open Settings (`Ctrl+,`) and search for "apimu". Edit the "Executable Path" to point to `testserver`.
> 4. Then open some `.mu` file (not those ones in the `notes` directory, they are too complex to be handled by `testserver`) and press `Ctrl+Shift+P`, then search for the "ApiMu: Restart" command.
>
> After executing the command, you may start typing some random characters like
>
> ```c++
> #define x "=" y := equals x y name equals_notation;
>
> anypred in/2 {
>
>   #define x "∈" y := in x y
>   name in_notation;
>
>   #define x "and" y "have" "the" "same" "elements" := forall a, a ∈ x <-> a ∈ y
>   name same_notation;
>
>   // Axiom...
>   assume (forall x, y, x and y have the same elements -> x = y)
>   name   set_ext {
>     // ...
>   }
> }
> ```
>
> If everything is fine, some blue squiggles would appear under `forall x, y, x and y have the same elements -> x = y` (update: there are no longer squiggles now, but mouse hovering should give some pop-ups). Note that proofs are not supported yet (update: proof checking is now supported, see [`notes/set_manual.mu`](notes/set_manual.mu)).


## To do list

- [x] [Core specification](notes/design.md)
  - [x] Metavariables / second-order variables
  - [x] Extension by definitions
- [ ] [The verifier](src/core/)
  - [x] Core part
  - [x] User-defined connectives (as unchecked axioms in the meta-logic...)
  - [ ] Text & binary file formats for FOL and ND trees
- [ ] The elaborator
  - [ ] Language server & VSCode extension (WIP)
    - [x] Boilerplate, IO, etc.
    - [x] Tracking document changes
    - [ ] Modifying, fading, etc.
  - [ ] Parser & pretty-printer (WIP)
    - [x] [Parsing algorithms](src/parsing/)
    - [x] Customizable syntax
    - [ ] Pretty-printer
  - [ ] MM1-style Scheme interpreter (I just want more flexible notations/macros... not sure if this is necessary)
    - [x] Primitive forms and procedures
    - [x] Macros
    - [ ] Formula and context representation
    - [ ] Calling external C++ and Python code for tactics (if I could make this far...)
  - [ ] Partial checking
  - [ ] Interactive proof-searching
    - [x] [Sequent calculus (analytic tableaux) with optimizations](src/elab/tableau.hpp) (WIP)
    - [ ] Translation from SC to ND (WIP)
    - [x] [First-order unification](src/elab/procs.hpp) (Robinson's)
    - [ ] Resolution and other "disjunctive-prove"/"conjunctive-refutation" methods (for generating instantiations; requires tableau to translate)
    - [ ] Higher-order unification
    - [ ] Equational reasoning
    - [ ] Try applying machine learning (could be a final year individual project...)
  - [ ] Proof transformation
    - [ ] "Definition erasure" for exporting proofs
    - [ ] Exporting proofs to MM0 (first-order only)
- [ ] Mathematics
  - [x] PA
  - [x] [ZFC](notes/set_manual.mu)
  - [ ] Naturals, integers and rationals under ZFC
  - [ ] Groups under ZFC
- [ ] Advanced elaborator features
  - [ ] Inductive definitions (≈ building a model of CIC in ZFC???)
  - [ ] Transferring results through isomorphism (if I could make this far...)


## Some random thoughts

(Don't take it serious, I am neither an expert in intuitionistic type theory nor one in set theory...)

(Certainly, set theory has its drawbacks as a logical framework of a theorem prover, but I think there are solutions... As commonly criticized, lack of type checking makes meaningless statements like `0 ∈ π` syntactically well-formed; however, if we allow the user to mark the definitions of `0` and `π` as "irreducible by default" (i.e. prohibits the use of their defining axioms by default), these errors could easily be detected without introducing the notion of types (you cannot go anywhere with hypothesis `0 ∈ π` without unfolding their definitions!). As another example, though the construction `Pair (a, b) := {{a}, {a, b}}` is unnatural, it plays no role other than making lemmas like `∀ a b c d, (Pair (a, b) = Pair (c, d) ↔ a = c ∧ b = d)` possible. We are safe to disregard the original definition immediately after we have derived all the necessary lemmas! The same technique may even make general inductive types (like those in the Calculus of Inductive Constructions) possible in set theory, and we could implement it as a feature of the elaborator. On the other hand, set theory also has certain advantages: most of the time, it more closely resembles informal reasoning (we don't *always* impose the restriction that everything has a *unique* type in informal mathematics!), it is easier to implement and to get right, and most importantly, the automation of first-order logic e.g. unification is easier and more developed, afaik...)

[~~John Harrison: Let's make set theory great again!~~](http://aitp-conference.org/2018/slides/JH.pdf)

