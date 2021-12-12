# ApiMu/FOL

I am too poor at mathematics so I have to make a "cheating engine" for myself!

Dependent type theory and [Lean](https://leanprover.github.io/) seem to be too
difficult to learn...

(I am not aiming to make any serious ITP software! I will just try to make the
UI as intuitive as possible while keeping the background theory simple. It
seems like FOL (natural deduction) + equality + extension by definitions are
already enough for this...)


## To do list

- [ ] The verifier
  - [x] Boilerplate code (data structures, console output, etc.)
  - [ ] Core part (WIP)
  - [ ] Text & binary file formats for FOL and ND trees (WIP)
- [ ] The elaborator
  - [ ] Boilerplate code & CLI
  - [ ] Syntax & parser for "derivation builder"
  - [ ] Tactics & infoview
- [ ] Formula & deduction schema support
  - [x] ~~Instantiation based~~
  - [ ] Metavariable based (WIP)
- [ ] Extension by definitions support
  - [ ] Test: PA
  - [ ] Test: ZFC
  - [ ] Test: von Neumann ordinals
  - [ ] Test: group under ZFC
- [ ] Simple "library search"
- [ ] More advanced provers
  - [ ] Test: clean up formalizations
- [ ] User-defined connectives?
- [ ] GUI? Visual Studio Code extension?


## Some random thoughts

(Don't take it serious, I am neither an expert in intuitionistic type theory
nor one in set theory...)

(Certainly, set theory has its drawbacks as a logical framework of a theorem
prover, but I think there are solutions... As commonly criticized, lack of
type checking makes meaningless statements like `0 ∈ π` syntactically
well-formed, which is more error-prone; however, if we allow the user to mark
the definitions of `0` and `π` as "irreducible by default" (i.e. prohibits the
use of their defining axioms by default), these errors could easily be detected
without introducing the notion of types (you cannot go anywhere with hypothesis
`0 ∈ π` without unfolding their definitions!). As another example, though the
construction `Pair (a, b) := {{a}, {a, b}}` is unnatural, it plays no role
other than making lemmas like
`∀ a b c d, (Pair (a, b) = Pair (c, d) ↔ a = c ∧ b = d)` possible. We are safe
to disregard the original definition immediately after we have derived all the
necessary lemmas! The same technique may even make general inductive types
(like those in the Calculus of Inductive Constructions) possible in set
theory, and we could implement it as a feature of the elaborator. On the other
hand, set theory also has certain advantages: most of the time, it more closely
resembles informal reasoning (we don't *always* impose the restriction that
everything has a *unique* type in informal mathematics!), it is easier to
implement and to get right, and most importantly, the automation of first-order
logic is more developed, afaik...)

