# ApiMu (FOL+)

I am too poor at mathematics so I have to make a "cheating engine" for myself!

Dependent type theory and [Lean](https://leanprover.github.io/) seem to be too difficult to learn... (Spent two months trying to make clear everything about its type theory, and then for example [it took me 40 lines to formalize a 5-line proof](https://github.com/bridgekat/lean-notes/blob/e8a9df5fff3feea2c5cc2d0112c101dd8d68f80c/src/2_analysis/1_the_real_and_complex_number_systems.lean#L448), even if I made use of automation tactics like `linarith`... And it seems hard to write new tactics...)

(I am not aiming to make any serious ITP software! This is just a "toy" system for inexperienced users (and AI) to interact with, so I will just try to make the UI as intuitive as possible while keeping the background theory simple. It seems like FOL with equality (natural deduction) + metavariables + extension by definitions are already enough for this...)


## To do list

- [x] [Core specification](notes/design.md) (almost completed)
  - [x] Metavariables / second-order variables
  - [x] Extension by definitions
- [ ] [The verifier](src/testcore.cpp)
  - [x] Core part (almost completed)
  - [ ] Text & binary file formats for FOL and ND trees
  - [ ] Core API
  - [ ] User-defined connectives (requires "implicit arguments"?)
- [ ] The elaborator
  - [ ] Parser & pretty-printer (WIP)
    - [x] [Parsing algorithms](src/parsing/) (almost completed)
    - [ ] Pretty-printer (WIP)
    - [ ] Customizable syntax
    - [ ] Notation support
  - [ ] Interactive proof-searching
    - [x] [Sequent calculus (analytic tableaux) with optimizations](src/elab/tableau.hpp) (WIP)
    - [ ] Translation between ND and SC (WIP)
    - [x] [First-order unification](src/elab/procs.hpp) (Robinson's)
    - [ ] Second-order unification
    - [ ] Equational reasoning
    - [ ] Tactics API
    - [ ] Resolution-based methods (how to translate these to ND?)
  - [ ] Language server & VSCode extension (WIP)
    - [x] Boilerplate, IO, etc.
    - [ ] Tracking document changes (WIP)
    - [ ] Basic functionalities
- [ ] Mathematics
  - [x] PA
  - [x] [ZFC](notes/set.mu)
  - [ ] Naturals, integers and rationals under ZFC
  - [ ] Groups under ZFC
- [ ] Advanced elaborator features
  - [ ] Inductive definitions
  - [ ] Transferring results through isomorphism


## Some random thoughts

(Don't take it serious, I am neither an expert in intuitionistic type theory nor one in set theory...)

(Certainly, set theory has its drawbacks as a logical framework of a theorem prover, but I think there are solutions... As commonly criticized, lack of type checking makes meaningless statements like `0 ∈ π` syntactically well-formed; however, if we allow the user to mark the definitions of `0` and `π` as "irreducible by default" (i.e. prohibits the use of their defining axioms by default), these errors could easily be detected without introducing the notion of types (you cannot go anywhere with hypothesis `0 ∈ π` without unfolding their definitions!). As another example, though the construction `Pair (a, b) := {{a}, {a, b}}` is unnatural, it plays no role other than making lemmas like `∀ a b c d, (Pair (a, b) = Pair (c, d) ↔ a = c ∧ b = d)` possible. We are safe to disregard the original definition immediately after we have derived all the necessary lemmas! The same technique may even make general inductive types (like those in the Calculus of Inductive Constructions) possible in set theory, and we could implement it as a feature of the elaborator. On the other hand, set theory also has certain advantages: most of the time, it more closely resembles informal reasoning (we don't *always* impose the restriction that everything has a *unique* type in informal mathematics!), it is easier to implement and to get right, and most importantly, the automation of first-order logic e.g. unification is easier and more developed, afaik...)

[~~John Harrison: Let's make set theory great again!~~](http://aitp-conference.org/2018/slides/JH.pdf)
