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



anypred L/2 B/3 any Q
{
  assume (forall x, forall y, L x y -> (forall z, not z = y -> not L x z))  name h1
  {
    assume (forall x, forall y, forall z, B x y z -> L x z -> L x y)        name h2
    {
      assume (exists x, not x = Q and forall y, B y x Q)                    name h3
      {                                                                     // ctx
        any c assume (not c = Q and forall x, B x c Q)                      name hc
        {                                                                   // ctx1
          => (not c = Q)                                                    name hc1 proof and.l hc;
          => (forall x, B x c Q)                                            name hc2 proof and.r hc;
          assume (exists x, L x Q)                                          name hex
          {                                                                 // ctx2
            any x assume (L x Q)                                            name hx
            {                                                               // ctx3
              => (forall z, not z = Q -> not L x z)                         name t1 proof implies.e (forall.e (forall.e h1 x) Q) hx;
              => (not L x c)                                                name t2 proof implies.e (forall.e t1 c) hc1;
              => (B x c Q)                                                  name t3 proof forall.e hc2 x;
              => (L x c)                                                    name t4 proof implies.e (implies.e (forall.e (forall.e (forall.e h2 x) c) Q) t3) hx;
              => (false)                                                    name t5 proof not.e t2 t4;
            }                                                               // implies.i and forall.i on t1, t2, t3, t4, t5
            => (false)                                                      name t6 proof exists.e hex t5 (false);
          }                                                                 // implies.i on t1, t2, t3, t4, t5, t6
          => (not exists x, L x Q)                                          name t7 proof not.i t6;
        }                                                                   // implies.i and forall.i on t1, t2, t3, t4, t5, t6, t7
        => (not exists x, L x Q)                                            name t8 proof exists.e h3 t7 (not exists x, L x Q);
      }
    }
  }
}


