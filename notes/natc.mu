/*
--------------------------------------------------------------------------------
This file contains the construction of the naturals from ZFC.
Though written in a formal syntax, this file is informal (i.e. NOT verified by a computer)!

19/12/2021
--------------------------------------------------------------------------------
*/


#ai local search_simple smt_z5 nn_gpt10f nn_alpha_turnstile_zero
// Activate some of the inference engines I downloaded from the future


#include "set.mu"

namespace natc private {
  
  public def zero       := (∅)        public name zero_def;
  public any a def succ := ({a, {a}}) public name succ_def;
  
  any x def inductive :<-> (zero ∈ x and forall a ∈ x, (succ a) ∈ x) name inductive_def;
  => (exists x, inductive x) by inductiveset_primitive;
  
  
  
  
  
}
