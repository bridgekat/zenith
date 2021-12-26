/*
--------------------------------------------------------------------------------
This file contains the theory of single-variable real analysis.
Though written in a formal syntax, this file is informal (i.e. NOT verified by a computer)!

20/12/2021
--------------------------------------------------------------------------------
*/


#ai local search_simple smt_z5 nn_gpt10f nn_alpha_turnstile_zero
// Activate some of the inference engines I downloaded from the future


import functions
import numbers // Load definitions from the maths library I downloaded from the future

namespace real private {
  // Notations must be explicitly declared locally
  
  infix    = eq;   // ?
  notation ℝ real;
  // Write 5 to mean (1 + 1 + 1 + 1 + 1)
  #el +numerals zero one
  infix    + add;
  prefix   - neg;
  infix    - sub;  // ?
  infix    * mul;
  suffix  ⁻¹ inv;
  infix    / div;  // ?
  // Write (a < b ≤ c = d) to mean (a < b and b ≤ c and c = d); elaborator will generate proof for (a < c) (a < d) (b ≤ d).
  #el +transitive_order_infix eq le lt ...
  
  // (TODO: do we actually need these?)
  prefix    nonempty;
  suffix is_nonempty;
  prefix    bounded_above;
  suffix is_bounded_above;
  
  // The real field in ApiMu (ASSUMED)
  // (TODO: two copies of each theorem on leaving "any" scope: "compact" and "full")
  any x y z assume (x ∈ ℝ) (y ∈ ℝ) (z ∈ ℝ) {
    
    => (is_field                  real add_fn zero neg_fn mul_fn one inv_fn);
    => (is_ordered_field          real add_fn zero neg_fn mul_fn one inv_fn le_fn);
    => (is_strictly_ordered_field real add_fn zero neg_fn mul_fn one inv_fn lt_fn);
    
    // Field axioms!
    => (x + y + z = x + (y + z));
    => (x + y = y + x);
    => (x + 0 = x);                   => (0 + x = x);
    => (x + -x = 0);                  => (-x + x = 0);
    
    => (x * y * z = x * (y * z));
    => (x * y = y * x);
    => (not 0 = 1);                   => (not 1 = 0);
    => (x * 1 = x);                   => (1 * x = x);
    => (not x = 0 -> x * x⁻¹ = 1);    => (not x = 0 -> x⁻¹ * x = 1);
    
    => (x * (y + z) = x * y + x * z); => ((x + y) * z = x * z + y * z);
    
    // Conversion between lt and le
    => (x ≤ y iff x < y or x = y);
    => (x < y iff x ≤ y and not x = y);
    
    // Total order axioms! (lt)
    => (not x < x);               // Irreflexivity
    => (x < y -> y < z -> x < z); // Transitivity
    => (x < y or x = y or y < x); // Trichotomy
    
    // Ordered field axioms! (lt)
    => (x < y -> forall z ∈ ℝ, x + z < y + z); // Add on right
    => (y < z -> forall x ∈ ℝ, x + y < x + z); // Add on left
    => (0 < x -> 0 < y -> 0 < x * y);          // Positive multiply
    
    // Total order axioms! (le)
    => (x ≤ x);
    => (x ≤ y -> y ≤ z -> x ≤ z);
    => (x ≤ y -> y ≤ x -> x = y);
    => (x ≤ y or y ≤ x);
    
    // Ordered field axioms! (le)
    => (x ≤ y -> forall z ∈ ℝ, x + z ≤ y + z);
    => (y ≤ z -> forall x ∈ ℝ, x + y ≤ x + z);
    => (0 ≤ x -> 0 ≤ y -> 0 ≤ x * y);
    
    // Completeness axiom! (existence & uniqueness of supremum)
    any S assume (S ⊆ ℝ) (S is_nonempty) (S is_bounded_above) {
      => (sup S ∈ ℝ);                                           // Supremum is defined in ℝ
      => (forall x ∈ S, x ≤ sup S);                             // Supremum is upper bound!
      => (forall u ∈ ℝ, (forall x ∈ S, x ≤ u) -> sup S ≤ u);    // Supremum is less or equal than upper bounds!
    }
    
    // Miscellaneous (TODO: inductive definitions)
    => (x - y = x + -y)                              by definition; // Conversion between minus and negation!
    => (x / y = x * y⁻¹)                             by definition; // Conversion between division and inverse!
    // "smul by integer" as repeated addition
    => (nsmul (nat.three)         x = x + x + x)     by definition;
    => (gsmul (nat.neg nat.three) x = -(x + x + x))  by definition;
    // "pow by integer" as repeated multiplication
    => (npow  (nat.three)         x = x * x * x)     by definition;
    => (gpow  (nat.neg nat.three) x = (x * x * x)⁻¹) by definition;
  }
  
  // Some corollaries (ASSUMED)
  any x y k assume (x ∈ ℝ) (y ∈ ℝ) (k ∈ ℝ) {
    => (k + x = k + y -> x = y);      => (x + k = y + k -> x = y);
    => (k + x = k     -> x = 0);      => (x + k =     k -> x = 0);
    => (k + x =   0   -> x = -k);     => (x + k =   0   -> x = -k);
    => (-(-k) = k);
    
    assume (not k = 0) {
      => (k * x = k * y -> x = y);      => (x * k = y * k -> x = y);
      => (k * x = k     -> x = 1);      => (x * k =     k -> x = 1);
      => (k * x =   1   -> x = k⁻¹);    => (x * k =   1   -> x = k⁻¹);
      => ((k⁻¹)⁻¹ = k);
    }
    
    => (0 * x = x * 0 = 0);    // (Useful!)
    => (x ≠ 0 -> y ≠ 0 -> x * y ≠ 0);
    => (-1 * x = x * -1 = -x); // (Useful!)
    => (-x * y = x * -y = -(x * y));
    => (-x * -y = x * y);
  
    => (-x < 0 iff 0 < x);
    => (0 < k -> (k * x < k * y iff x < y));    => (0 < k -> (x * k < y * k iff x < y));    // (Mul or cancel)
    => (k < 0 -> (k * x < k * y iff y < x));    => (k < 0 -> (x * k < y * k iff y < x));    // (Mul or cancel)
    => (not x = 0 -> 0 < x * x);                // (Nonzero squares are positive)
    => (not x = 0 -> (0 < x⁻¹ iff 0 < x));      // (Inverse preserves sign)
    => (-1 < 0 < 1);                            // (-1 < 0 and 0 < 1)
    => (0 < x -> x < y -> y⁻¹ < x⁻¹);           // (Inverse reverses order if both positive)
    
    // "Exclusive" trichotomy
    => (x < y iff not y ≤ x);
    => (x ≤ y iff not y < x);
  }
  
  any x y assume (x ∈ ℝ) (y ∈ ℝ) (0 < x) private {
    assume (forall n ∈ ℕ, n * x ≤ y) {
      def A := ({z ∈ ℝ | exists n ∈ N, z = n * x}); => (nonempty A); => (bounded_above A);
      def a := (sup A);                             => (forall x ∈ A, x ≤ a); => (forall u, (forall x ∈ A, x ≤ u) -> a ≤ u);
      def b := (a + -x);                            => (b < a); => (a = b + x);
      => (exists m ∈ ℕ, b < m * x);
      => (exists m ∈ ℕ, a < m * x + x);
      => (exists m' ∈ ℕ, a < m' * x);               => (false);
    }
    public => (exists n ∈ ℕ, y < n * x)
    name      "the Archimedean property";
  }
  
  any x y assume (x ∈ ℝ) (y ∈ ℝ) (x < y) private {
    => (0 < y - x);
    => (exists n ∈ ℕ, 1 < n * (y - x)) by "the Archimedean property";
    any n assume (1 < n * (y - x)) {
      // Use (1 / n) as "unit"
      => (exists m2 ∈ ℕ, n * x < m2 * 1) by "the Archimedean property";
      => (exists m1 ∈ ℕ, -n * x < m1 * 1) by "the Archimedean property";
      => (exists m1 ∈ ℕ, exists m2 ∈ ℕ, -m1 < n * x < m2);
      any m1 m2 assume (m1 ∈ ℕ) (m2 ∈ ℕ) (-m1 < n * x < m2) {
        => (exists m ∈ ℤ, m - 1 ≤ n * x < m); // (TODO: make clear)
        any m assume (m ∈ ℤ) (m - 1 ≤ n * x < m) {
          => (m ≤ n * x + 1 < n * y);
          => (x < m / n < y);
          => (exists p ∈ ℚ, x < p < y);
        }
      }
    }
    public => (exists p ∈ ℚ, x < p < y)
    name      "ℚ is dense in ℝ";
  }
  
  any n assume (n ∈ ℕ) (n ≠ 0) any x assume (x ∈ ℝ) (0 ≤ x) private {
    // (TODO: proof)
    
    public => (unique y ∈ ℝ, npow n y = x)
    name      "a non-negative real number always have its n-th root in ℝ";
    
    public def root :: (npow n root = x)
    name       root_def
               "definition for the root function";
  }
  
  any n assume (n ∈ ℕ) (n ≠ 0) any x assume (x ∈ ℝ) (0 ≤ x) private {
    public => (npow n (root n x) = x)
    name      "power of root, cancel";
    public => (root n (npow n x) = x)
    name      "root of power, cancel";
  }
  
  any n assume (n ∈ ℕ) (not n = 0) any x y assume (x ∈ ℝ) (y ∈ ℝ) (0 ≤ x) (0 ≤ y) private {
    def x' := (root n x);
    def y' := (root n y);
    => (npow n x' = x);
    => (npow n y' = y);
    => (x * y = npow n x' * npow n y' = npow n (x' * y'));
    => (root n (x * y) = root n (npow n (x' * y')) = x' * y');
    public => (root n (x * y) = root n x * root n y)
    name      "root of product, split";
  }
  
  // (TODO: inductively define the decimal expansion sequence)
  // (TODO: the extended real number system)
}

// (TODO: the complex field and Euclidean spaces)



