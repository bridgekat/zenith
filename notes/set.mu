/*
--------------------------------------------------------------------------------
This file contains the definitions and axioms from the Zermelo-Fraenkel set theory (with choice).
Though written in a formal syntax, this file is informal (i.e. NOT verified by a computer)!

17/12/2021
--------------------------------------------------------------------------------
*/


#ai local search_simple smt_z5 nn_gpt10f nn_alpha_turnstile_zero
// Activate some of the inference engines I downloaded from the future


anypred in/2 {
  infix ∈ in;
  
  any x y def notin := (not x ∈ y);
  infix ∉ notin;
  
  any x y def subsetof := (forall z ∈ x, z ∈ y);
  infix ⊆ subsetof;
  
  // We can write "forall a ∈ x, ..." to mean "forall a, a ∈ x -> ..."
  //     or write "exists a ∈ x, ..." to mean "exists a, a ∈ x and ..."
  // This is true for all unary and binary predicate symbols.
  
  // Axiom...
  assume (forall x y, (forall a, a ∈ x <-> a ∈ y) -> x = y)
  name   set_ext
         "axiom of extensionality"
         "set extensionality"
         "sets which have the same elements are equal" {
    
    // Axiom...
    assume (forall x, (exists a ∈ x) -> (exists y ∈ x, not exists a, a ∈ x and a ∈ y))
    name   set_regular
           "axiom of regularity"
           "axiom of foundation"
           "every non-empty set x contains a member y such that x and y are disjoint sets" {
      
      // Axiom schema...
      assume (forallpred φ/2, forall x, exists y, forall a, a ∈ y <-> a ∈ x and φ x a)
      name   subset_primitive
             "axiom schema of subsets (primitive form)"
             "axiom schema of specification (primitive form)"
             "axiom schema of separation (primitive form)"
             "any definable subset of a given set exists (primitive form)" {
        
        // A more useful form (with uniqueness, so that we could write it as a function using definite description)
        anypred φ/2 any x {
          any y1 assume (forall a, a ∈ y1 <-> (a ∈ x and φ x a)) {
            any y2 assume (forall a, a ∈ y2 <-> (a ∈ x and φ x a)) {
              => (forall z, z ∈ y1 <-> z ∈ y2);
              => (y1 = y2) by set_ext;
            }
          }
          => (unique y, forall a, a ∈ y <-> (a ∈ x and φ x a));
          
          def  subset :: (forall a, a ∈ subset <-> (a ∈ x and φ x a))
          name subset_def
               "definition of a subset";
        }
        
        // The empty set can now be defined (ApiMu assumes the domain of discourse to be nonempty)
        => (forall x, unique y, forall a, a ∈ y <-> (a ∈ x and false));
        => (unique x, forall y, y ∉ x);
        
        def  emptyset :: (forall y, y ∉ emptyset);
        name emptyset_def
             "definition of the empty set"
             "the empty set contains no element";
        
        // Axiom...
        assume (forall x y, exists z, x ∈ z and y ∈ z)
        name   pairset_primitive
               "axiom of pairing (primitive form)"
               "the set containing two given sets exists (primitive form)" {
          
          // A more useful form ("exactly" x and y...)
          any x y {
            any z' assume (x ∈ z' and y ∈ z') {
              private def z := subset (a | a = x or a = y) z'; // Use `subset` to eliminate anything apart from x and y
              => (exists z, forall a, a ∈ z' <-> a = x or a = y);
            }
            => (exists z, forall a, a ∈ z <-> a = x or a = y) by exists.e;
            => (unique z, forall a, a ∈ z <-> a = x or a = y) by set_ext;
            
            def  pairset :: (forall a, a ∈ pairset <-> a = x or a = y)
            name pairset_def
                 "definition of a pair set"
                 "the pair set of x and y contains exactly x and y";
          }
          
          // An often-convenient definition
          any x {
            def singletonset := (pairset x x);
            => (forall a, a ∈ singletonset x <-> a = x or a = x);
            => (forall a, a ∈ singletonset x <-> a = x) name singletonset_def;
          }
          
          // Axiom...
          assume (forall F, exists z, forall x ∈ F, forall a ∈ x, a ∈ z)
          name   unionset_primitive
                 "axiom of union (primitive form)"
                 "there exists a set that includes the union of a family of sets (primitive form)" {
            
            // A more useful form ("exactly" the union...)
            any F {
              any z' assume (forall x ∈ F, forall a ∈ x, a ∈ z') {
                private def z := subset (a | exists x ∈ F, a ∈ x) z'; // Use `subset` to eliminate anything apart from elements of x's
                any a {
                  assume (a ∈ z) { => (exists x ∈ F, a ∈ x); }
                  assume (exists x ∈ F, a ∈ x) { any x assume (x ∈ F and a ∈ x) { => (a ∈ z'); } => (a ∈ z); }
                }
                => (exists z, forall a, a ∈ z <-> (exists x ∈ F, a ∈ x));
              }
              => (exists z, forall a, a ∈ z <-> (exists x ∈ F, a ∈ x)) by exists.e;
              => (unique z, forall a, a ∈ z <-> (exists x ∈ F, a ∈ x)) by set_ext;
              
              def  unionset :: (forall a, a ∈ unionset <-> (exists x ∈ F, a ∈ x))
              name unionset_def
                   "definition of a union ∪F"
                   "the union of a family of sets contains exactly elements of the sets";
            }
            
            // Axiom schema...
            // Since definite description is already built into the logic, the schema of replacement can be written equivalently as:
            assume (forallfunc φ/2, forall x, exists y, forall a ∈ x, φ x a ∈ y)
            name   imageset_primitive
                   "axiom schema of image sets (primitive form)"
                   "axiom schema of replacement (primitive form)"
                   "there exists a codomain set for a definable function over a given set (primitive form)" {
              
              // A more useful form ("exactly" the image set...)
              anyfunc φ/2 any x {
                any y' assume (forall a ∈ x, φ x a ∈ y') {
                  private def y := subset (b | exists a ∈ x, b = φ x a) y';
                  any b {
                    assume (b ∈ y) { => (exists a ∈ x, b = φ x a); }
                    assume (exists a ∈ x, b = φ x a) { any a assume (a ∈ x and b = φ x a) { => (b ∈ y'); } => (b ∈ y); }
                  }
                  => (forall b, b ∈ y <-> (exists a ∈ x, b = φ x a));
                  => (exists y, forall b, b ∈ y <-> (exists a ∈ x, b = φ x a));
                }
                => (exists y, forall b, b ∈ y <-> (exists a ∈ x, b = φ x a)) by exists.e;
                => (unique y, forall b, b ∈ y <-> (exists a ∈ x, b = φ x a)) by set_ext;
                
                def  imageset :: (forall b, b ∈ imageset <-> (exists a ∈ x, b = φ x a))
                name imageset_def
                     "definition of the image of a function φ"
                     "the image set of a function φ contains exactly those elements obtained by applying φ over the domain x";
              }
              
              // Axiom...
              assume (exists x, emptyset ∈ x and forall a ∈ x, (pairset a (singletonset a)) ∈ x)
              name   inductiveset_primitive
                     "axiom of infinity (primitive form)"
                     "there exists an inductive set (primitive form)" {
                
                // Axiom...
                assume (forall x, exists y, forall z ⊆ x, z ∈ y)
                name   powerset_primitive
                       "axiom of power set (primitive form)"
                       "the subsets of a set are all contained in some set (primitive form)" {
                  
                  // A more useful form ("exactly" the power set...)
                  any x {
                    any y' assume (forall z ⊆ x, z ∈ y') {
                      private def y := subset (a | a ⊆ x) y';
                      => (exists y, forall a, a ∈ y <-> a ⊆ x);
                    }
                    => (exists y, forall a, a ∈ y <-> a ⊆ x) by exists.e;
                    => (unique y, forall a, a ∈ y <-> a ⊆ x) by set_ext;
                    
                    def  powerset :: (forall a, a ∈ powerset <-> a ⊆ x)
                    name powerset_def
                         "definition of the power set of x"
                         "the power set of x contains exactly the subsets of x as elements";
                  }
                  
                  // The axiom of choice (AC) is invoked (on the metatheoretic level!) when the `idef` keyword is used.
                  // `idef` is sufficient to prove the AC here:
                  any x assume (emptyset ∉ x) private {
                    any y assume (y ∈ x) {
                      => (exists a ∈ y);
                      idef f :: (f ∈ y) name f_def;
                      #ls // f_def : (f ∈ y)
                    }
                    #ls // f_def : (forall y ∈ x, f y ∈ y)
                    // To complete the remaining steps, one could take the Cartesian product of x and ∪x, and use `subset` to make f_fn...
                  }
                  
                  // The elaborator has special support for several set-theoretic notations:
                  #el +subset_builder_fn subset // (TODO: the notation {a ∈ x | φ a})
                  #el +singletonset_builder_fn singletonset // (TODO: the notation {x})
                  #el +pairset_builder_fn pairset // (TODO: the notation {x, y} and {x})
                  #el +listset_builder_fn singletonset pairset unionset // (TODO: the notations {a, b, c, d, e}, etc.)
                  #el +binary_union_fn pairset unionset // (TODO: the notations (x ∪ y), etc.)


/*
--------------------------------------------------------------------------------
This is a non-closing theory (i.e. it adds primitive symbols and axioms when imported).
--------------------------------------------------------------------------------
*/

