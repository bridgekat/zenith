General idea: every line you write down after `=>` will become a theorem, which may or may not have a name. The computer will remember every theorem and try to "follow" your thoughts, with several algorithms running in parallel.



## Logical theory and commands

ApiMu will use a standard first-order logic with equality, extended with function and predicate metavariables to support formula schemas like the separation and replacement ones in ZFC axioms.

A **context `(F, P, Γ)`** is composed of **the set `F` of functions**, **`P` of predicates**, and **`Γ` of assumptions**. (It replaces the notions of "signature" and "theory".)

- Each element of `F` and `P` is a pair of a string (name) and a nonnegative integer (arity).
  - These will be written as `φ/2`, `f/3`, etc.
    - In type theories (higher-order logics), these can be written as `φ : ι → ι → *`, `f : ι → ι → ι → ι`, etc. where `ι` stands for the type of individuals and `*` the type/universe of propositions.
  - Nullary functions like `x/0` (`x : ι`) stand for individual variables. These are different from other functions in a first-order theory (e.g. they can be universally or existentially quantified over).
  - Nullary predicates like `p/0` (`p : *`) stand for propositions.
- Each element of `Γ` is a pair of a string (name) and a well-formed "formula" or "formula schema" defined w.r.t. `F` and `P`.
  - These will be written as `name : p ∧ q`, etc. like in type theories.
  - The set of "terms" (expressions of type `ι`) under some `F` is inductively defined as:
    - For any element `f/n ∈ F` and terms `t₁, t₂, ..., tₙ` under `F`, the expression `(f t₁ t₂ ... tₙ)` is also a term. The base case is when `n = 0`.
  - The set of "formulas" (expressions of type `*`) under some `F` and `P` is inductively defined as:
    - For any element `p/n ∈ P` and terms `t₁, t₂, ..., tₙ` under `F`, the expression `(p t₁ t₂ ... tₙ)` is an (atomic) formula. This also includes the case `n = 0`.
    - If `t₁` and `t₂` are terms under `F`, then `(t₁ = t₂)` is an (atomic) formula.
    - `true` and `false` are formulas.
      > Alternatively written as `⊤` and `⊥`.
    - If `e` is a formula under `F` and `P`, then so is `(not e)`.
      > Alternatively written as `(¬e)`.
    - If `e₁` and `e₂` are formulas under `F` and `P`, then so are `(e₁ and e₂)`, `(e₁ or e₂)`, `(e₁ implies e₂)` and `(e₁ iff e₂)`.
      > Alternatively written as `(e₁ ∧ e₂)`, `(e₁ ∨ e₂)`, `(e₁ → e₂)` and `(e₁ ↔ e₂)`.
    - For any string `x` not occurring in `F`, if `e` is a formula under `F ∪ {x/0}` and `P`, then `(forall x, e)`, `(exists x, e)` and `(unique x, e)` are formulas under `F` and `P`.
      > Alternatively written as `(∀ x, e)`, `(∃ x, e)` and `(∃! x, e)`.
  - The set of "formula schemas" (expression schemas of type `*`) under some `F` and `P` is inductively defined as:
    - Any formula under `F` and `P` is also a formula schema.
    - For any string `f` not occurring in `F`, and any positive integer `n`, if `e` is a formula schema under `F ∪ {f/n}` and `P`, then `(forallfunc f/n, e)` is a formula schema under `F` and `P`. (The `n = 0` case is already covered in the previous rule, so it's not included here.)
      > Alternatively written as `(∀# f/n, e)`.
    - For any string `p` not occurring in `P`, and any nonnegative integer `n`, if `e` is a formula schema under `F` and `P ∪ {p/n}`, then `(forallpred p/n, e)` is a formula schema under `F` and `P`.
      > Alternatively written as `(∀$ p/n, e)`.
  - The last two rules should be understood as a way to express "formula schemas" (infinite sets of formulas obtained by specializing those function and predicate variables). Although they could as well represent second-order quantifications, I'm not going to fully support second-order logic (you can see there's no second-order existential quantifiers, and the `∀#` and `∀$` must appear at the beginning). Instead I will use sets to represent functions and higher-order functions...
- As explained above, the definition of a formula schema depends on `F` and `P`. A context `(F, P, Γ)` is well-formed only if all formula schemas in `Γ` are well-formed under `F` and `P`.
- For simplicity we assume that no two elements in `F`, `P` or `Γ` share the same name. Below, context extensions like `Γ ∪ {h : p ∧ q}` are assumed to be well-formed (no duplicate names).
  - (In the actual implementation, later names will "override" earlier names)
- The domain of discourse `ι` is considered to be non-empty (inhabited). The individual variable `initial : ι` can be used anywhere.
- For later convenience, I will also define some kind of "lambda expressions"...
  - (TODO: complete) (Maybe I will end up implementing some kind of λΠ...?)



## Natural Deduction rules (with equality)

When I was doing an assignment of IUM, I found this style of writing makes proofs especially clear... #####

Now I came up with this: ##### (This is like `section`s and `parameter`s in Lean, but interacts better with definitions)

Just like in Lean, the important cases here are `implies` and `forall`. In ApiMu, their introduction rules are "context-changing" (you get a new hypothesis/variable, then prove the consequence/property). Other similar rules in natural deduction (like or-elimination, exists-elimination) can be defined in terms of them.

Context-changing keywords:

- `{ ... }`
- `assume (...) { ... }`
- `any x { ... }`
- `anyfunc f/n {...}`
- `anypred p/n { ... }`

The other rules are represented in something like "proof terms". (TODO: complete) (Maybe I will end up implementing some kind of λΠ...?)

To prove a theorem using non-context-changing rules, write `=> (<theorem-statement>) name <name> proof <proof-term>;` where `<theorem-statement>` is a formula schema, `<name>` is an identifier, **and `<proof-term>` is inductively defined w.r.t. the local context `(F, P, Γ)` and known theorems `Δ` by:**

(TODO: type out the ND rules...)

After proof-checking, this theorem will be added into a "known theorem pool" `Δ` maintained by ApiMu. This is like the `Γ` in the context, but not the same thing; it represents a set of theorems derivable under the current context and assumptions, including but not limited to the assumptions themselves. ApiMu will guarantee that every explicitly stated theorem gets added to `Δ`, but there may also be additional theorems generated by the inference engines.

- `Δ` is also stored in a stack. Denote its top layer by `Δ'`, and the second-to-top layer by `Δ''`.

The introduction rules for `implies`, `forall`, `forallfunc` and `forallpred` are automatically applied to all applicable theorems in the top level of `Δ`, when leaving from some section. (Below, the `...` in front of `φ` is used to denote all "second-order quantifiers" in front of a formula schema.)

- When leaving from `assume (h : <assumption>)` section, for every theorem (schema) `...φ` in `Δ'`, the theorem (schema) `...(<assumption> → φ)` will be added back to `Δ''`.
  - The "second-order quantifiers" will remain in the front. (This can be understood as simultaneously putting assumptions in front of an infinite family of formulas.)
  - **Exception: if `<assumption>` itself contains "second-order quantifiers", nothing will be added back!** First-order logic is not sufficient to express such outcomes, and "assuming an infinite set of propositions" is only useful in expressing axiom schemas...
- When leaving from `any x` section, for every theorem (schema) `...φ` in `Δ'`, the theorem (schema) `...(forall x, φ)` will be added back to `Δ''`.
  - The "second-order quantifiers" will remain in the front. (This can be understood as simultaneously putting quantifiers in front of an infinite family of formulas.)
- When leaving from `anyfunc f/n` section, for every theorem (schema) `...φ` in `Δ'`, the theorem (schema) `(forallfunc f/n, ...φ)` will be added back to `Δ''`.
- When leaving from `anypred p/n` section, for every theorem (schema) `...φ` in `Δ'`, the theorem (schema) `(forallpred p/n, ...φ)` will be added back to `Δ''`.



## Extension by definitions

(TODO: complete)

- `def g := ...`: adds new function symbol `g/0` and its defining axiom to context
- `def g :↔ ...`: adds new predicate symbol `g/0` and its defining axiom to context
- `def g :: ...`: adds new function symbol `g/0` and its defining axiom to context, by definite description.
  - The proof for ... must be provided.

- `idef g :: ...`: adds new function symbol `g/0` and its defining axiom to context, by indefinite description. (This is not a conservative extension, or only "conservative" when AC is involved in the metatheory (there's no constructive argument for it), and it is sufficient to prove the AC inside the theory...)
  - The proof for ... must be provided.
- On leaving from `assume` sections, their arities are unchanged; `→` will be added in front of all local theorems (including their defining axioms).
- On leaving from `any` sections, their arities will be added by one; a new argument (the variable generalised on) is inserted at the beginning; `forall` will be added in front of all local theorems (including their defining axioms).
- On leaving from `anyfunc` or `anypred` sections, they will not be preserved. We can't represent higher-order functions directly in the first-order language, and this is also unnecessary.

(Put definitions inside `assume` sections to get partial functions & predicates (i.e. you have nothing to say about them unless you have all the preconditions. The metatheoretic interpretation could be a three-valued logic with an "undefined" value, and every formula with "undefined" value cannot be proved or disproved...))



## Axioms

- Axioms are outermost definitions & assumptions
- Some inference engines only work when you have a certain set of axioms (i.e. your local context contains certain things). You may need to provide their names / IDs.
- We generally use ZFC as the starting set of axioms.



That's all for the foundations.

-----

## Opaque definitions

- (TODO: revise)
- Theorems can be modified using `private`. These will be cleared when leaving the current section. (Alternatively, use `private` when opening a section, and use `public` to modify theorems that you want to export.)
- Definitions can be modified using `private`. Defining axioms can also be modified using `private`. (There are three possible combinations. The `private`-`public` combination is the same as `private`-`private`, as the defining axiom will still be removed along with the function/predicate symbol.)
- The `public`-`private` combination allows for "opaque definitions", which is suitable for preventing "fake theorems".



## Miscellaneous

- `undef _`: removes a predicate / function symbol / metavariable from context; removes everything in the context that depends on it (i.e. remove any non-well-formed formulas)
- `#ls` (shows the current context)
- `#ai _` (activate inference engine(s), options: `none`, `bfs`. In all cases the default inference engine (simple unifier) will be active in a thread.)
- `#set _ _` (set parameter...)



## Inductive definitions in ZFC

- (TODO: try to complete this part based on Mario Carneiro's thesis)



## Appendix: axiomatic details

(TODO: proof of conservations. Outline: find the outermost scope for each definition, then "pull out" the definition and translate)