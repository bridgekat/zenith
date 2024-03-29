In this section, we digress a little bit to relationships among propositional logics (PL), first-order logics (FOL), second-order logics (SOL), higher-order logics (HOL), simple type theories (STT) and dependent type theories (DTT).

## The problem

The obvious differences are the forms of quantifications allowed:

- In PL, we do not have quantifiers.
- In FOL, we have $\forall$ and $\exists$ which can range over individual objects.
- In SOL, we additionally have $\forall^1$ and $\exists^1$ which can range over predicates.
- In HOL, we are able to quantify over predicates-of-predicates, predicates-of-predicates-of-predicates, etc. Arities of predicates are also called types.
  - STT is a many-sorted formulation of HOL, where we quantify over functions. Predicates are represented by functions which return Booleans. This means we need to encode logical rules as an equational theory of functions.
  - DTT is another many-sorted formulation of HOL, which allows the return types of functions to depend on the value of their arguments. Predicates are represented by type families in the `Prop` universe, whose "elements" are their proofs. This results in a uniform syntax for functions and natural deduction proofs.

Generality in quantifications is often associated with "power". One would say e.g. "SOL is more powerful than FOL". However, I personally had a difficult time understanding this: on one hand, SOL indeed has metatheoretic properties like categoricity which FOL does not *(FOL instead has Löwenheim-Skolem, which means FOL theories cannot restrict the cardinality of its models)*; on the other hand, think about ZFC set theory in FOL, it is able to do "all mathematics" and is definitely more "powerful" than SOL! Moreover, we can encode SOL/HOL/STT/DTT in FOL by adding a binary predicate for "predicate application", together with infinitely many "comprehension axioms" *(just like the axiom schema of specification in ZFC)* so that "order" does not seem to make a real difference; and note that the instantiation of "comprehension axioms" in FOL is syntactically identical to $\forall^1$-elimination in SOL.

To pick a "best" logic for a theorem prover, such confusion must be resolved. Here are my current understanding:

- For theorem provers, most semantic/metatheoretic/model-theoretic properties are of little relevance, the only important thing is relative consistency.
  - Such properties are for people who want to study the interaction of a logic, defined inside some background mathematics *(which we do not have one)*, with the background mathematics itself. Like the interaction of a virtual machine with the host OS.
- Even if we try to come up with a purely syntactic notion of power, it cannot be exactly defined, and the best definition I currently have is the ease of embedding one logic inside another *(where "ease" is informal)*.
  - Since PL/FOL/SOL/HOL/STT are all fragments of DTT, the simple "inclusion maps" embed them into DTT without notational overhead *(type inference means you do not even need to annotate types)*, which makes DTT the best choice in my opinion.

## Semantic power

To semantically compare two logical theories $\mathcal T_1$ and $\mathcal T_2$, we need:

- Semantics of each logical theory, which give satisfaction relations $\models_1$ and $\models_2$;
- An injective map $\phi \mapsto [\phi]$ from formulas in $\mathcal T_1$ to formulas in $\mathcal T_2$.

Then we can say "$\mathcal T_2$ is no less powerful than $\mathcal T_1$" when, for all formula $\phi$ of $\mathcal T_1$:

$$
\mathcal T_1 \models_1 \phi \quad\rightarrow\quad \mathcal T_2 \models_2 [\phi]
$$

In other words: the counterpart of any true $\mathcal T_1$-statement is a true $\mathcal T_2$-statement.

Consider $\mathcal T_1 = \mathsf{FOL}$ and $\mathcal T_2 = \mathsf{SOL}$ with full semantics, and $[\cdot]$ to be the inclusion map, then the condition clearly holds. But if we instead let $\mathcal T_1 = \mathsf{SOL}$ with full semantics on infinite domains, and $\mathcal T_2 = \mathsf{FOL}$ with symbols $\mathrm{obj}, \mathrm{pred}_n, @_n$ and comprehension schema, and $[\cdot]$ be the translation which turns $\forall x, \phi(x)$ into $\forall x, \mathrm{obj}(x) \rightarrow\phi(x)$, $\forall^1 P_n, \phi(P_n)$ into $\forall P, \mathrm{pred}_n(P)\rightarrow\phi(P)$, and $P_n(x_1,\ldots,x_n)$ into $@_n(P, x_1,\ldots,x_n)$ as usual, then we can still find a true SOL-statement $\phi$ *(e.g. exists injective function which is not surjective)* for which the FOL-statement $[\phi]$ is not always true *(even if we also interpret the individuals as elements in an infinite set, we are still free to interpret the predicates as those corresponding to bijective functions; comprehension schema is not enough for constructing a counterexample)*. Together this means that SOL with infinite-domain, full semantics is strictly more powerful than FOL with infinite-domain, "non-full" semantics. On the other hand, if we used a "non-full" (Henkin) semantics on SOL, the same translation would work, and SOL has no additional power than FOL.

For translating HOL into FOL, we need a new sort of "types", a typing predicate $:$ and application symbols $@_n$, as well as rules forming the types and assigning types to terms. To translate lambda predicates, we invoke comprehension schema to obtain some $P$ such that $@_n(P, x_1, \ldots, x_n) \leftrightarrow \phi(x_1, \ldots, x_n)$ where $\phi$ is innermost body *(variables are fully applied)* of the lambda. Without studying the exact details, it seems like the situation is the same: a full semantics gives more power, while "non-full" semantics gives the same power as the translated FOL theory.

I have yet to fully understand the semantics of type theories. The calculus of constructions (CoC) has established consistency results, so I assume it is safe to use; however, I am not sure about either CIC or CoC + ZFC. In the worst case, a DTT type checker can always be restricted to act as an FOL natural deduction checker, so I will be fine as long as I only ever use first-order quantifiers in my proofs.

## Syntactic power

To syntactically compare two logical theories $\mathcal T_1$ and $\mathcal T_2$, we need:

- Derivation rules for logical theory, which give provability relations $\vdash_1$ and $\vdash_2$;
- An injective map $\phi \mapsto [\phi]$ from formulas in $\mathcal T_1$ to formulas in $\mathcal T_2$.

Then we can say "$\mathcal T_2$ is no less powerful than $\mathcal T_1$" when, for all formula $\phi$ of $\mathcal T_1$:

$$
\mathcal T_1 \vdash_1 \phi \quad\rightarrow\quad \mathcal T_2 \vdash_2 [\phi]
$$

In other words: the counterpart of any provable $\mathcal T_1$-statement is a provable $\mathcal T_2$-statement. (If we replace $\rightarrow$ with $\leftrightarrow$, this would become the definition of "$\mathcal T_2$ is a conservative extension of $\mathcal T_1$".)

However, under this definition, almost every logic can be extended with additional assumptions to become sufficiently powerful. For example, we can add the Peano axioms and induction schema to FOL to obtain PA, then use some arithmetic encoding in PA to describe all DTT derivations rules, and now we are able to formulate the provability relation of DTT in PA. Since a theorem prover should be able to accept arbitrary user-defined assumptions, this means most logics are equal for a theorem prover.

The only reason that currently no theorem prover is encoding all its proofs in PA is a practical one: such encoding would be huge, inefficient to verify and impossible to read. On the other hand, encoding PA in a DTT theorem prover is super easy. Moreover, all common logics including PL/FOL/SOL/HOL/STT admit shallow embeddings inside DTT. This suggests DTT to be the current best choice for a logical foundation.

The only problem: by doing e.g. FOL derivations inside DTT, we may be able to prove more theorems than expected. This can be solved by adding restrictions to the type checker while doing proofs in a restricted logic *(e.g. limiting quantifiers to first-order)*, which is still easy.
