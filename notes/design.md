General idea: every line you write down after `=>` will become a theorem, which may or may not have a name. The computer will remember every theorem and try to "follow" your thoughts, with several algorithms running in parallel.



## Logical theory and commands

A **context $(\Sigma; \Gamma)$** is composed of **the set $\Sigma$ of all assumed variables** (individuals, functions, predicates) and **the set $\Gamma$ of all assumed formulas**. (It replaces the notions of "signature" and "theory".)

In the following specification, context extensions like $\Gamma \cup \ldots$ are assumed to be well-formed (i.e. no duplicate names).

The domain is always considered to be non-empty.



### Well-formed terms and formulas (with equality)

(TODO: complete)



### Natural Deduction rules (with equality)

(TODO: complete; context-changing and non-context-changing rules)

- Context-changing keywords: `{ ... }`, `any x { ... }`, `assume (...) { ... }`
  - When leaving a section, everything is preserved, but possibly with added $\forall$ or $\rightarrow$ in the front
- Other keywords: `=> ()` (declarative); `by` (imperative); `name ""` (give a name)
  - Imperative commands: `andi () ()`, `andl ()`, `andr ()`, ...



### Metavariables

- `mterm g`: adds new function (term) metavariable `g/0` to context
- `mform g`: adds new predicate (formula) metavariable `g/0` to context
- On exiting `any` sections, their arities will be added by one; a new argument is inserted at the beginning; $\forall$ will be added in front of all local theorems.
- On exiting `assume` sections, their arities are unchanged; $\rightarrow$ will be added in front of all local theorems.
- More deduction keywords:
  - `mtsubs a g (t)`: substitute `g` in `a` using `t(x1, ..., xn, y1, ..., ym)`
  - `mfsubs a g (p)`: substitute `g` in `a` using `p(x1, ..., xn, y1, ..., ym)`

(TODO: `mdef` as sugar)



### Extension by definitions

(TODO: complete)

- `term g := ...`: adds new function (term) symbol `g/0` and its defining axiom to context
- `form g :<-> ...`: adds new predicate (formula) symbol `g/0` and its defining axiom to context
- On exiting `any` sections, their arities will be added by one; a new argument (the variable generalised on) is inserted at the beginning; $\forall$ will be added in front of all local theorems (including their defining axioms).
- On exiting `assume` sections, their arities are unchanged; $\rightarrow$ will be added in front of all local theorems (including their defining axioms).

(Put definitions inside `assume` and `end` to get partial functions & predicates (i.e. you have nothing to say about them unless you have all the preconditions))

(TODO: `def` as sugar)

(TODO: similarly for definite and indefinite descriptions)



### Axioms

- Axioms are outermost definitions & assumptions
- Some inference engines only work when you have a certain set of axioms (i.e. your local context contains certain things). You may need to provide their names / IDs.
- We generally use ZFC as the starting set of axioms.



That's all for the foundations.

-----

### Opaque definitions

- (TODO: revise)
- Theorems can be modified using `private`. These will be cleared when leaving the current section. (Alternatively, use `private` when opening a section, and use `public` to modify theorems that you want to export.)
- Definitions can be modified using `private` or `opaque`. The latter means that the definition will not be cleared, but its defining axiom will be.
- This will allow "opaque definitions", which is suitable for preventing "fake theorems".



### Miscellaneous

- `undef _`: removes a predicate / function symbol / metavariable from context; removes everything in the context that depends on it (i.e. remove any non-well-formed formulas)
- `#ls` (shows the current context)
- `#ai _` (activate inference engine(s), options: `none`, `bfs`. In all cases the default inference engine (simple unifier) will be active in a thread.)
- `#set _ _` (set parameter...)



### Inductive definitions in ZFC

- (TODO: complete this part based on Mario Carneiro's thesis)



## Appendix: axiomatic details

(TODO: proof of conservations)