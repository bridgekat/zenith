## The `search_simple` inference engine

Maintains a set of theorems on every level; inner level theorems have higher "priority" during library searches.

- The search procedure will be based on the method of analytic tableaux (i.e. sequent calculus without cuts).
  - By stating out each step, the user is actually guiding the insertion of cuts.
  - To improve efficiency, store the tableau using an efficient data structure. (In most existing theorem provers, tactics cannot persist their states across different invocations!)
- It is possible for the library to grow huge (I'm aiming to support 10³~10⁴ theorems... If I'm not mistaken, Lean's mathlib contains approximately ~6×10⁴ in total, but not all of them are imported in typical situations), and most theorems start with either `∀` or `→`.

(TODO: how to integrate resolution (or other bottom-up approaches) into an interactive UI...?)
