import set

// (TODO: move definitions)

// Ordered pair
private {
  // Constructors
  public any x y def pair := ({{x}, {x, y}}) private name pair_def;
  // "Typing judgment"
  public any x def is_pair := (exists a b, x = pair a b) public name is_pair_def;
  // Eliminator ("recursor")
  public anyfunc φ/2 any x assume (is_pair x) def pair_rec := ...
}

namespace pair private {
  public def pair.fst ...
}

// (TODO: list syntax [a, b, c, d, e]...)

/*
// Binary tree
private namespace tree {
  // Constructors
  public any x                                    def leaf := ([leaf_tag, x])       private name leaf_def;
  public any l x r assume (is_tree l) (is_tree r) def node := ([node_tag, l, x, r]) private name node_def;
  
}
*/

// A set is a function when...
any f def is_function :<-> (forall p ∈ f, is_pair p and (forall y, [pair.fst p, y] ∈ f -> y = pair.snd p))
     name is_function_def;
// Note that "function sets" are still individual variables, and are different from function variables!
// ("functions at the theory level" vs. "functions at the language level"...)

// Handling functions in set theories is not as easy as in higher-order logics (i.e. type theories), since "functions are not first-class citizens"...
// To fix it, we will show that "theory-level functions" can be converted to "language-level functions", using the definite description rule:
any f assume (is_function f) {
  => (forall p ∈ f, is_pair p);
  => (forall p ∈ f, forall y, [pair.fst p, y] ∈ f -> y = pair.snd p);
  
  // Definition for domain and range...
  def domain := imageset (f p | pair.fst p) f;
  def range  := imageset (f p | pair.snd p) f;
  
  any x assume (x ∈ domain f) {
    // Claim: there is a unique y such that [x, y] ∈ f!
    // Expand definitions...
    => (x ∈ (imageset (f p | pair.fst p) f)) by domain_def;
    => (exists p ∈ f, x = pair.fst p) by imageset_def;
    
    // First part, existence...
    any p assume (p ∈ f) (x = pair.fst p) {
      => ([x, pair.snd p] = p);
      => ([x, pair.snd p] ∈ f);
      => (exists y, [x, y] ∈ f);
    }
    => (exists y, [x, y] ∈ f);
    
    // Second part, uniqueness...
    any y1 assume ([x, y1] ∈ f) {
      => (forall y, [pair.fst [x, y1], y] ∈ f -> y = pair.snd [x, y1]);
      => (forall y, [x, y] ∈ f -> y = y1) by definition;
    }
    => (unique y, [x, y] ∈ f);
    
    // Now we can define "function application" as a language-level function!
    def funapp :: ([x, funapp] ∈ f) name funapp_def;
  }
}
=> (forall is_function f, forall x ∈ domain f, forall y, ([x, y] ∈ f <-> y = funapp f x));
=> (forall is_function f, forall x ∈ domain f, [x, funapp f x] ∈ f); // (The <- direction, useful to consider as a separate lemma)

#el operator_notation ↑ funapp
// Now we may write (↑f x) for any f and x to mean (funapp f x)! (No space needed between ↑ and f...)
// As for other language-level partial functions, you can apply ↑ to any set, regardless of whether is_function holds for it;
// But you can only use the following theorems if is_function holds for it...
=> (forall is_function f, forall x ∈ domain f, forall y, ([x, y] ∈ f <-> y = ↑f x));
=> (forall is_function f, forall x ∈ domain f, [x, ↑f x] ∈ f); // (The <- direction, useful to consider as a separate lemma)


// (TODO: sending language-level functions down to the theory level)
// (TODO: requires: Cartesian product)


// As an example, I will build some higher-order functions...
private {
  any N {
    any x assume (x ∈ N) {
      // (TODO: define `f : N → N := λ y, x + y` as a theory-level function)
    }
    // (TODO: define `g : N → N → N := λ x, f x` as a theory-level function)
  }
}


// The following examples are adapted from https://github.com/ImperialCollegeLondon/M40001_lean/tree/master/src/2021/functions
// Note that in set theory, a function does not "know" its codomain!
// See: https://edstem.org/us/courses/15124/discussion/702800

any f assume (is_function f) {
  def  injective :<-> (forall a ∈ domain f, forall b ∈ domain f, ↑f a = ↑f b -> a = b)
  name injective_def;
  
  any codomain assume (range f ⊆ codomain) {
    def  surjective :<-> (forall y ∈ codomain, exists x, ↑f x = y);
    name surjective_def;
  }
  
  // (TODO: complete)
}

// You can see that there are nasty ↑'s all over the place. All because functions are not first-class citizens!
// In type theories, sets (or more precisely, subsets) are not first-class citizens, and these ↑'s will appear on sets and their elements instead.

// And if you want to have both powers from sets and higher-order languages, you will end up with two versions of definitions for
//   "injective" and "surjective", one theory-level and one language-level -- even worse!


// (Bad End:  it turns out that our system is harder to use than type theoretic ones, since functions appear everywhere in mathematics...
//            Even if we could omit those ↑'s in the syntax without creating ambiguity, this will only lead to even more confusion...)

// (Good End: those ↑'s create much smaller mental burden compared to introducing a whole complex system of dependent types, while preserving
//            more flexibility than limiting ourselves in simple types.)

// (True End: fortunately, in our language, omitting those ↑'s does not create ambiguity! And our simple 1.5th-order language has allowed for AI
//            powerful enough to do all such conversions between theory- and language-level in the background for us!)


