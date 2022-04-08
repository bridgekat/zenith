# ApiMu

I am too poor at mathematics so I have to make a "cheating engine" for myself!

Dependent type theory and [Lean](https://leanprover.github.io/) seem to be too difficult to learn... (Spent two months trying to make clear everything about its type theory, and then for example [it took me 40 lines to formalize a 5-line proof](https://github.com/bridgekat/lean-notes/blob/e8a9df5fff3feea2c5cc2d0112c101dd8d68f80c/src/2_analysis/1_the_real_and_complex_number_systems.lean#L448), even if I made use of automation tactics like `linarith`... And it seems hard to write new tactics...)

[Metamath One](https://github.com/digama0/mm0/blob/master/mm0-hs/mm1.md) looks nice! I did not realize this earlier...

(I am not aiming to make any serious ITP software! This is just a "toy" system for inexperienced users (and AI) to interact with, so I will just try to make the UI as intuitive as possible while keeping the background theory simple. It seems like FOL with equality (natural deduction) + metavariables + extension by definitions are already enough for this...)


## To do list

- [x] [Core specification](notes/design.md) (almost completed)
  - [x] Metavariables / second-order variables
  - [x] Extension by definitions
- [ ] [The verifier](src/testcore.cpp)
  - [x] Core part (almost completed)
  - [ ] Text & binary file formats for FOL and ND trees
  - [ ] User-defined connectives (requires "implicit arguments"?)
  - [ ] "Definition erasure" for exporting proofs
- [ ] The elaborator
  - [ ] Parser & pretty-printer (WIP)
    - [x] [Parsing algorithms](src/parsing/) (almost completed)
    - [ ] Pretty-printer (WIP)
    - [ ] Customizable syntax
    - [x] Notation support (almost completed)
  - [ ] Interactive proof-searching
    - [x] [Sequent calculus (analytic tableaux) with optimizations](src/elab/tableau.hpp) (WIP)
    - [ ] Translation between ND and SC (WIP)
    - [x] [First-order unification](src/elab/procs.hpp) (Robinson's)
    - [ ] Second-order unification
    - [ ] Equational reasoning
    - [ ] Resolution-based methods (how to translate these to ND?)
  - [ ] Language server & VSCode extension (WIP)
    - [x] Boilerplate, IO, etc.
    - [x] Tracking document changes
    - [ ] Partial checking
    - [ ] Modifying, fading, etc.
  - [ ] MM1-style Scheme interpreter (I just want more flexible notations/macros... not sure if this is necessary)
  - [ ] Exporting proofs to MM0
  - [ ] Python API for tactics (if I could make this far...)
- [ ] Mathematics
  - [x] PA
  - [x] [ZFC](notes/set_manual.mu)
  - [ ] Naturals, integers and rationals under ZFC
  - [ ] Groups under ZFC
- [ ] Advanced elaborator features
  - [ ] Inductive definitions (i.e. building a model of Martin-Löf type theory in ZFC + ???)
  - [ ] Transferring results through isomorphism (if I could make this far...)


## Building (experimental)

Make sure a C++20 compiler (I'm using GCC 11.2) and CMake 3.12+ is available on your computer. In the root directory, run:

```sh
mkdir build
cd build
cmake ..
make # or others
```

If everything is fine, you can then find three executables (`testcore`, `testparsing` and `testserver`) in the `build` directory. The relevant one is `testserver`, which is a rudimentary LSP server that is supposed to parse `.mu` files.

1. Open the `vscode` directory in VSCode.
2. Press `Ctrl+Shift+B` and then `F5` (or probably directly pressing `F5` is enough) to start the Extension Development Host.
3. Open Settings (`Ctrl+,`) and search for "apimu". Edit the "Executable Path" to point to `testserver`.
4. Then open some `.mu` file (not those ones in the `notes` directory, they are too complex to be handled by `testserver`) and press `Ctrl+Shift+P`, then search for the "ApiMu: Restart" command.

After executing the command, you may start typing some random characters like

```c++
#define x "=" y := equals x y name equals_notation;

anypred in/2 {

  #define x "∈" y := in x y
  name in_notation;

  #define x "and" y "have" "the" "same" "elements" := forall a, a ∈ x <-> a ∈ y
  name same_notation;

  // Axiom...
  assume (forall x, y, x and y have the same elements -> x = y)
  name   set_ext {
    // ...
  }
}
```

If everything is fine, some blue squiggles would appear under `forall x, y, x and y have the same elements -> x = y` (update: there are no longer squiggles now, but mouse hovering should give some pop-ups). Note that proofs are not supported yet (update: proof checking is now supported, see [`notes/set_manual.mu`](notes/set_manual.mu)).

You may also try executing `testcore`. It contains some tests for the experimental tableau prover (currently it is rather inefficient, and does not support equational reasoning. Nevertheless, it already proves some first-order propositions that Lean's `finish` tactic cannot prove...)


## Some random thoughts

(Don't take it serious, I am neither an expert in intuitionistic type theory nor one in set theory...)

(Certainly, set theory has its drawbacks as a logical framework of a theorem prover, but I think there are solutions... As commonly criticized, lack of type checking makes meaningless statements like `0 ∈ π` syntactically well-formed; however, if we allow the user to mark the definitions of `0` and `π` as "irreducible by default" (i.e. prohibits the use of their defining axioms by default), these errors could easily be detected without introducing the notion of types (you cannot go anywhere with hypothesis `0 ∈ π` without unfolding their definitions!). As another example, though the construction `Pair (a, b) := {{a}, {a, b}}` is unnatural, it plays no role other than making lemmas like `∀ a b c d, (Pair (a, b) = Pair (c, d) ↔ a = c ∧ b = d)` possible. We are safe to disregard the original definition immediately after we have derived all the necessary lemmas! The same technique may even make general inductive types (like those in the Calculus of Inductive Constructions) possible in set theory, and we could implement it as a feature of the elaborator. On the other hand, set theory also has certain advantages: most of the time, it more closely resembles informal reasoning (we don't *always* impose the restriction that everything has a *unique* type in informal mathematics!), it is easier to implement and to get right, and most importantly, the automation of first-order logic e.g. unification is easier and more developed, afaik...)

[~~John Harrison: Let's make set theory great again!~~](http://aitp-conference.org/2018/slides/JH.pdf)

