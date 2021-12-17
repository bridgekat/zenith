General idea: every line you write down after `=>` will become a theorem, which may or may not have a name. The computer will remember every theorem and try to "follow" your thoughts, with several algorithms running in parallel.

I will NOT adopt any form of Curry-Howard correspondence (and intuitionistic type theory) as that will complicate things, not do I use the LCF approach (though this unifies the proof language and metaprogramming language, the language will most likely be less convenient to use than mainstream ones)...

Using C++ as the "metaprogramming language", we actually have more flexibility on writing automation...



## Logical theory and commands

A **context $(\Sigma; \Gamma)$** is composed of **the set $\Sigma$ of all assumed variables** (individuals, functions, predicates) and **the set $\Gamma$ of all assumed formulas**. (It replaces the notions of "signature" and "theory".)

In the following specification, context extensions like $\Gamma \cup \ldots$ are assumed to be well-formed (i.e. no duplicate names).



### Well-formed terms and formulas (with equality)

(TODO: complete)



### Natural Deduction rules (with equality)

(TODO: complete; context-changing and non-context-changing rules)

- Context-changing keywords: `section`, `any`, `assume`; `end` (preserves everything, adding $\forall$ or $\rightarrow$ in front of them), `qed` (preserves only the last line, also adding $\forall$ or $\rightarrow$ in front of it)
- Other keywords: `=>` (declarative); `by` (imperative); `name` (give a name)
  - Imperative commands: `andi _ _`, `andl _`, `andr _`, ...



### Extension by definitions

(TODO: complete)

- `func g(x1, ..., xn)`: adds new function symbol `g/n` to context
- `func g(x1, ..., xn) := ...`: adds new function symbol `g/n` and its defining axiom to context
- `pred g(x1, ..., xn)`: adds new predicate symbol `g/n` to context
- `pred g(x1, ..., xn) := ...`: adds new predicate symbol `g/n` and its defining axiom to context

(Put definitions inside `assume` and `end` to get partial functions & predicates (i.e. you have nothing to say about them unless you have all the preconditions))

(TODO: similarly for definite and indefinite descriptions)



### Metavariables

- `metafunc g(x1, ..., xn)`: adds new function metavariable `g/n` to the context
- `metapred g(x1, ..., xn)`: adds new predicate metavariable `g/n` to the context
- More deduction keywords:
  - `fsubs a g t`: substitute `g` in `a` using `t(x1, ..., xn, y1, ..., ym)`
  - `psubs a g p`: substitute `g` in `a` using `p(x1, ..., xn, y1, ..., ym)`



### Axioms

- Axioms are outermost definitions & assumptions
- Some inference engines only work when you have a certain set of axioms (i.e. your local context contains certain things). You may need to provide their names / IDs.
- We generally use ZFC as the starting set of axioms.



That's all for the foundations.

-----

### Opaque definitions

- Theorems can be modified using `private`. These will be cleared when leaving the current scope. (Alternatively, use `private` when opening a scope, and use `public` to modify theorems that you want to export.)
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