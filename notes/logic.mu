// From iff.e to iff.l and iff.r

anypred p/0 q/0 {
  assume (p <-> q) (p) name hpq hp {
    => (q) by iff.e ($) hpq hp;
  }
}
=> (forallpred p/0 q/0, (p <-> q) -> p -> q) name iff.l;

anypred p/0 q/0 {
  assume (p <-> q) (q) name hpq hq {
    assume (p) { => (p); } => (p <-> p) name hpp;
    => (q <-> p) by iff.e ($ <-> p) hpq hpp name hqp;
    => (p) by iff.e ($) hqp hq;
  }
}
=> (forallpred p/0 q/0, (p <-> q) -> q -> p) name iff.r;


// Uniqueness intro
anypred φ/1 private {
  => (exists x, φ x);
  
  // Plan A: (exists x, ... and forall y, ... -> y = x)
  any x assume (φ x) {
    any y assume (φ y) {
      => ...
      => (y = x);
    }
    => (forall y, φ y -> y = x);
    => (φ x and forall y, φ y -> y = x);
    => (exists x, φ x and forall y, φ y -> y = x);
  }
  => (exists x, φ x and forall y, φ y -> y = x) by exists.e;
  => (Conclusion);
  
  // Plan B: ((exists x, ...) and (forall x, ... -> forall y, ... -> x = y))
  any x assume (φ x) any y assume (φ y) {
    => ...
    => (x = y);
  }
  => (forall x, φ x -> forall y, φ y -> x = y);
  => (Conclusion);
  
  // From A to B
  => ()
}


// Flexible proof-terms

anypred p/0 {
  // Lemma:
  => (p or not p)
  name lem
  proof {
    raa
      assume (not (p or not p)) name h {
        assume (p) name hp {
          => (false) proof not.e h (or.l hp) name t2;
        }
        => (not p) proof not.i t2 name t3;
        => (p or not p) proof or.r t3 name t4;
        => (false) proof not.e h t4;
      }
  };
}

// Lemma:
=> (forall x y, x = y or not x = y)
name decidable_eq
proof {
  any x y
    => (x = y or not x = y) proof lem (x = y);
};

