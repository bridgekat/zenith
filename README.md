# ApiMu/FOL

I am too poor at mathematics so I have to make a "cheating engine" for myself!

(Dependent type theory and [Lean](https://leanprover.github.io/) seem to be too
difficult to learn...)


## To Do List

- [ ] The verifier
  - [x] Boilerplate code (data structures, console output, etc.)
  - [ ] Binary format for FOL and ND trees
- [ ] The elaborator
  - [ ] Boilerplate code & CLI
  - [ ] Syntax & parser for "deduction builder"
  - [ ] Tactics & infoview
  - [ ] Test: the "no one loves QZR" deduction
- [ ] Formula & deduction schema support
  - [ ] Instantiation based
  - [ ] Template based
- [ ] Extension by definitions support
  - [ ] Test: PA
  - [ ] Test: ZFC
  - [ ] Test: PA under ZFC
  - [ ] Test: group under ZFC
- [ ] Simple ND proof searcher
- [ ] More advanced provers
  - [ ] Test: clean up formalizations
- [ ] GUI? Visual Studio Code extension?