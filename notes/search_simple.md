## The `search_simple` inference engine

Maintains a set of theorems on every level; inner level theorems have higher "priority" during library searches.

- The search procedure will be based on the method of analytic tableaux (i.e. sequent calculus without cuts).
  - By stating out each step, the user is actually guiding the insertion of cuts.
  - To improve efficiency, store the tableau using an efficient data structure. (In most existing theorem provers, tactics cannot persist their states across different invocations!)
- Though it is possible for the library to grow huge, most theorems start with either $\forall$ or $\rightarrow$.
  - $\rightarrow$-prefixed theorems become usable only if we had the necessary preconditions.
    - Many theorems have common preconditions; expand them all simultaneously. (Otherwise the size of the tableau may grow exponentially...)
    - Furthermore, the (→L) rule may be optimized... (And branching rules should be delayed in general)
  - $\forall$-prefixed theorems are dealt with using unification.
  - In the future, neural-network-guided searching may become possible.
