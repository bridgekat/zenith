## The `search_simple` inference engine

Maintains a set of theorems on every level; inner level theorems have higher "priority" during library searches.

- Though it is possible for the library to grow huge, most theorems start with either $\forall$ or $\rightarrow$.
  - $\rightarrow$-prefixed theorems become usable only if we had the necessary preconditions.
  - $\forall$-prefixed theorems can be specialized to any variable; this is the harder part.

