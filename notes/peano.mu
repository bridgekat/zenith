/*
--------------------------------------------------------------------------------
This file contains the definitions and axioms from the first-order Peano arithmetic.
Though written in a formal syntax, this file is informal (i.e. NOT verified by a computer)!

19/12/2021
--------------------------------------------------------------------------------
*/


#ai local search_simple smt_z5 nn_gpt10f nn_alpha_turnstile_zero
// Activate some of the inference engines I downloaded from the future


anyfunc zero/0 succ/1 add/2 mul/2 pow/2 {
  def one := (succ zero);
  
  notation 0 zero;
  notation 1 one;
  infix + add;
  infix * mul;
  infix ^ pow;
  
  assume (forall x, not 0 = succ x) name zero_ne_succ {
    assume (forall x y, succ x = succ y -> x = y) name succ_inj {
      assume (forallpred p/1, p 0 -> (forall x, p x -> p (succ x)) -> forall x, p x) name induction {
        
        assume (forall x, x + 0 = x) (forall x y, x + (succ y) = succ (x + y)) name add_zero add_succ {
          assume (forall x, x * 0 = 0) (forall x y, x * (succ y) = x * y + x) name mul_zero mul_succ {
            assume (forall x, x ^ 0 = 1) (forall x y, x ^ (succ y) = x ^ y * x) name pow_zero pow_succ {
              
              private {
                => (0 + 0 = 0);
                any x assume (0 + x = x) { => (0 + succ x = succ (0 + x) = succ x); } // (TODO: calculational proof support)
                public => (forall x, 0 + x = x) name zero_add by induction (x | 0 + x = x);
              }
              
              private {
                any x { => (succ x + 0 = succ x = succ (x + 0)); }
                any y assume (forall x, succ x + y = succ (x + y)) {
                  any x { => (succ x + succ y = succ (succ x + y) = succ (succ (x + y)) = succ (x + succ y)); }
                }
                public => (forall x y, succ x + y = succ (x + y)) name succ_add by induction (y | forall x, succ x + y = succ (x + y));
                // (TODO: automatic permutation of quantifiers)
              }


/*
--------------------------------------------------------------------------------
This is a non-closing theory (i.e. it adds primitive symbols and axioms when imported).
--------------------------------------------------------------------------------
*/

