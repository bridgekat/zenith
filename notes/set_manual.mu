// Manually proved everything!
// A proof in this file is 2~4x longer than an equivalent one in Lean
// (due to the syntax, lack of elaboration and definitional unfolding, etc.)

#define x "=" y := equals x y name equals_notation;

any x, y assume x = y name heq
  => y = x name eq_symm proof equals.e (□ | □ = x) heq (equals.i x);

any x, y, z assume x = y name hxy, y = z name hyz
  => x = z name eq_trans proof equals.e (□ | x = □) hyz hxy;

anypred in/2 {

  #define x "∈" y := in x y
  name in_notation

  #define x "∉" y := not in x y
  name notin_notation

  #define x "⊆" y := forall _z, _z ∈ x -> _z ∈ y
  name subsetof_notation

  #define x "and" y "have" "the" "same" "elements" := forall _a, _a ∈ x <-> _a ∈ y
  name same_notation

  // Axiom...
  assume (forall x, y, x and y have the same elements -> x = y)
  name   set_ext {

    #define x "is" "nonempty" := exists _a, _a ∈ x
    name nonempty_notation

    #define x "and" y "are" "disjoint" := not (exists _a, _a ∈ x and _a ∈ y)
    name disjoint_notation

    // Axiom...
    assume forall x, x is nonempty -> exists y, y ∈ x and x and y are disjoint
    name   set_regular {

      // Axiom schema...
      assume forallpred φ/2, forall x, exists y, forall a, a ∈ y <-> a ∈ x and φ x a
      name   subset_primitive {

        // A more useful form (with uniqueness, so that we could write it as a function using definite description)
        anypred φ/2 any x {
          any y1 assume forall a, a ∈ y1 <-> a ∈ x and φ x a name h1 {
            any y2 assume forall a, a ∈ y2 <-> a ∈ x and φ x a name h2 {
              any z {
                assume z ∈ y1 name hz => z ∈ y2 name hzl proof iff.r (forall.e h2 z) (iff.l (forall.e h1 z) hz);
                assume z ∈ y2 name hz => z ∈ y1 name hzr proof iff.r (forall.e h1 z) (iff.l (forall.e h2 z) hz);
                => z ∈ y1 <-> z ∈ y2 name hz' proof iff.i hzl hzr;
              }
              => y1 = y2 name heq proof implies.e (forall.e (forall.e set_ext y1) y2) hz';
            }
          }
          // `subset` is well-defined
          => unique y, forall a, a ∈ y <-> a ∈ x and φ x a name subset_unique
              proof unique.i (forall.e (forallpred.e subset_primitive (x, y | φ x y)) x) heq;

          def  subset :: (forall a, a ∈ subset <-> (a ∈ x and φ x a))
          name subset_def proof subset_unique;
        }

        // The empty set can now be defined (ApiMu assumes the domain of discourse to be nonempty)
        => unique y, forall a, a ∈ y <-> a ∈ initial and false name he proof forall.e (forallpred.e subset_unique (x, y | false)) initial;
        any y assume forall a, a ∈ y <-> a ∈ initial and false name hy {
          any a {
            assume a ∈ y name ha => false name ha' proof and.r (iff.l (forall.e hy a) ha);
            => a ∉ y name ha'' proof not.i ha';
          }
          => exists x, forall y, y ∉ x name hex proof exists.i (exists x, forall y, y ∉ x) y ha'';
        }
        => exists x, forall y, y ∉ x name hex' proof exists.e (unique.l he) hex (exists x, forall y, y ∉ x);
        any x1 assume forall y, y ∉ x1 name hx1 {
          any x2 assume forall y, y ∉ x2 name hx2 {
            any a {
              assume a ∈ x1 name ha => a ∈ x2 name hal proof false.e (not.e (forall.e hx1 a) ha) (a ∈ x2);
              assume a ∈ x2 name ha => a ∈ x1 name har proof false.e (not.e (forall.e hx2 a) ha) (a ∈ x1);
              => a ∈ x1 <-> a ∈ x2 name ha proof iff.i hal har;
            }
            => x1 = x2 name heq proof implies.e (forall.e (forall.e set_ext x1) x2) ha;
          }
        }
        => unique x, forall y, y ∉ x name emptyset_unique proof unique.i hex' heq;

        def  emptyset :: forall y, y ∉ emptyset
        name emptyset_def proof emptyset_unique;

        any x => x ∉ emptyset name emptyset_prop proof forall.e (iff.r (forall.e emptyset_def emptyset) (equals.i emptyset)) x;

        // Axiom...
        assume (forall x, y, exists z, x ∈ z and y ∈ z)
        name   pairset_primitive {

          // A more useful form ("exactly" x and y...)
          any x, y {
            any z' assume x ∈ z' and y ∈ z' name hz' {
              def z := subset (_, a | a = x or a = y) z' name z_def; // Use `subset` to eliminate anything apart from x and y
              => forall a, (a ∈ z iff (a ∈ z' and (a = x or a = y))) name hz proof iff.r (forall.e (forall.e (forallpred.e subset_def (_, a | a = x or a = y)) z') z) z_def;
              any a {
                assume a ∈ z name ha => a = x or a = y name hal proof and.r (iff.l (forall.e hz a) ha);
                assume a = x or a = y name ha {
                  assume a = x name ha.left  => a ∈ z' name haz'.left  proof equals.e (□ | □ ∈ z') (implies.e (forall.e (forall.e eq_symm a) x) ha.left) (and.l hz');
                  assume a = y name ha.right => a ∈ z' name haz'.right proof equals.e (□ | □ ∈ z') (implies.e (forall.e (forall.e eq_symm a) y) ha.right) (and.r hz');
                  => a ∈ z name har proof iff.r (forall.e hz a) (and.i (or.e ha haz'.left haz'.right) ha);
                }
                => a ∈ z <-> a = x or a = y name ha proof iff.i hal har;
              }
              => exists z, forall a, a ∈ z <-> a = x or a = y name hex proof exists.i (exists z, forall a, a ∈ z <-> a = x or a = y) z ha;
            }
            => exists z, forall a, a ∈ z <-> a = x or a = y name hex proof exists.e (forall.e (forall.e pairset_primitive x) y) hex (exists z, forall a, a ∈ z <-> a = x or a = y);
            any z1 assume forall a, a ∈ z1 <-> a = x or a = y name hz1 {
              any z2 assume forall a, a ∈ z2 <-> a = x or a = y name hz2 {
                any a {
                  assume a ∈ z1 name ha => a ∈ z2 name hal proof iff.r (forall.e hz2 a) iff.l (forall.e hz1 a) ha;
                  assume a ∈ z2 name ha => a ∈ z1 name har proof iff.r (forall.e hz1 a) iff.l (forall.e hz2 a) ha;
                  => a ∈ z1 <-> a ∈ z2 name ha proof iff.i hal har;
                }
                => z1 = z2 name heq proof implies.e (forall.e (forall.e set_ext z1) z2) ha;
              }
            }
            => unique z, forall a, a ∈ z <-> a = x or a = y name pairset_unique proof unique.i hex heq;

            def  pairset :: forall a, a ∈ pairset <-> a = x or a = y
            name pairset_def proof pairset_unique;
          }

          // An often-convenient definition
          any x def singletonset := pairset x x name singletonset_def;
          any x any a {
            assume a ∈ singletonset x name ha {
              => a ∈ pairset x x name ha' proof equals.e (□ | a ∈ □) (forall.e singletonset_def x) ha;
              => a = x or a = x name ha'' proof iff.l (forall.e (iff.r (forall.e (forall.e (forall.e pairset_def x) x) (pairset x x)) (equals.i (pairset x x))) a) ha';
              assume a = x name id => a = x name id proof id;
              => a = x name hl proof or.e ha'' id id;
            }
            assume a = x name ha {
              => a = x or a = x name hor proof or.l ha (a = x);
              => a ∈ pairset x x name ha' proof iff.r (forall.e (iff.r (forall.e (forall.e (forall.e pairset_def x) x) (pairset x x)) (equals.i (pairset x x))) a) hor;
              => a ∈ singletonset x name hr proof equals.e (□ | a ∈ □) (implies.e (forall.e (forall.e eq_symm (singletonset x)) (pairset x x)) (forall.e singletonset_def x)) ha';
            }
            => a ∈ singletonset x <-> a = x name singletonset_def proof iff.i hl hr;
          }

          // Axiom...
          assume forall F, exists z, forall x, x ∈ F -> (forall a, a ∈ x -> a ∈ z)
          name   unionset_primitive {

            // A more useful form ("exactly" the union...)
            any F {
              any z' assume forall x, x ∈ F -> (forall a, a ∈ x -> a ∈ z') name hz' {
                def z := subset (_, a | exists x, x ∈ F and a ∈ x) z' name z_def; // Use `subset` to eliminate anything apart from elements of x's
                any a {
                  => a ∈ z <-> a ∈ z' and (exists x, x ∈ F and a ∈ x) name lemma proof forall.e (iff.r (forall.e (forall.e (forallpred.e subset_def (_, a | exists x, x ∈ F and a ∈ x)) z') z) z_def) a;
                  assume a ∈ z name ha => exists x, x ∈ F and a ∈ x name ha' proof and.r (iff.l lemma ha);
                  assume exists x, x ∈ F and a ∈ x name ha'' {
                    any x assume x ∈ F and a ∈ x name hx => a ∈ z' name haz' proof implies.e (forall.e (implies.e (forall.e hz' x) (and.l hx)) a) (and.r hx);
                    => a ∈ z name haz proof iff.r lemma (and.i (exists.e ha'' haz' (a ∈ z')) ha'');
                  }
                  => a ∈ z <-> (exists x, x ∈ F and a ∈ x) name hiff proof iff.i ha' haz;
                }
                => exists z, forall a, a ∈ z <-> (exists x, x ∈ F and a ∈ x) name hex proof exists.i (exists z, forall a, a ∈ z <-> (exists x, x ∈ F and a ∈ x)) z hiff;
              }
              => exists z, forall a, a ∈ z <-> (exists x, x ∈ F and a ∈ x) name hex' proof exists.e (forall.e unionset_primitive F) hex (exists z, forall a, a ∈ z <-> (exists x, x ∈ F and a ∈ x));
              any z1 assume forall a, a ∈ z1 <-> (exists x, x ∈ F and a ∈ x) name hz1 {
                any z2 assume forall a, a ∈ z2 <-> (exists x, x ∈ F and a ∈ x) name hz2 {
                  any a {
                    assume a ∈ z1 name ha => a ∈ z2 name hal proof iff.r (forall.e hz2 a) (iff.l (forall.e hz1 a) ha);
                    assume a ∈ z2 name ha => a ∈ z1 name har proof iff.r (forall.e hz1 a) (iff.l (forall.e hz2 a) ha);
                    => a ∈ z1 <-> a ∈ z2 name ha proof iff.i hal har;
                  }
                  => z1 = z2 name heq proof implies.e (forall.e (forall.e set_ext z1) z2) ha;
                }
              }
              => unique z, forall a, a ∈ z <-> (exists x, x ∈ F and a ∈ x) name unionset_unique proof unique.i hex' heq;

              def  unionset :: (forall a, a ∈ unionset <-> (exists x, x ∈ F and a ∈ x))
              name unionset_def proof unionset_unique;
            }

            // Axiom schema...
            // Since definite description is already built into the logic, the schema of replacement can be written equivalently as:
            assume forallfunc φ/2, forall x, exists y, forall a, a ∈ x -> φ x a ∈ y
            name   imageset_primitive {

              // A more useful form ("exactly" the image set...)
              anyfunc φ/2 any x {
                any y' assume forall a, a ∈ x -> φ x a ∈ y' name hy' {
                  def y := subset (_, b | exists a, a ∈ x and b = φ x a) y' name y_def;
                  any b {
                    => b ∈ y <-> b ∈ y' and (exists a, a ∈ x and b = φ x a) name lemma proof forall.e (iff.r (forall.e (forall.e (forallpred.e subset_def (_, b | exists a, a ∈ x and b = φ x a)) y') y) y_def) b;
                    assume b ∈ y name hb => exists a, a ∈ x and b = φ x a name hb' proof and.r (iff.l lemma hb);
                    assume exists a, a ∈ x and b = φ x a name hex {
                      any a assume a ∈ x and b = φ x a name ha => b ∈ y' name hb proof equals.e (□ | □ ∈ y') (implies.e (forall.e (forall.e eq_symm b) (φ x a)) (and.r ha)) (implies.e (forall.e hy' a) (and.l ha));
                      => b ∈ y name hby proof iff.r lemma (and.i (exists.e hex hb (b ∈ y')) hex);
                    }
                    => b ∈ y <-> (exists a, a ∈ x and b = φ x a) name hiff proof iff.i hb' hby;
                  }
                  => exists y, forall b, b ∈ y <-> (exists a, a ∈ x and b = φ x a) name hex proof exists.i (exists y, forall b, b ∈ y <-> (exists a, a ∈ x and b = φ x a)) y hiff;
                }
                => exists y, forall b, b ∈ y <-> (exists a, a ∈ x and b = φ x a) name hex' proof exists.e (forall.e (forallfunc.e imageset_primitive (x, y | φ x y)) x) hex (exists y, forall b, b ∈ y <-> (exists a, a ∈ x and b = φ x a));
                any y1 assume forall b, b ∈ y1 <-> (exists a, a ∈ x and b = φ x a) name hy1 {
                  any y2 assume forall b, b ∈ y2 <-> (exists a, a ∈ x and b = φ x a) name hy2 {
                    any a {
                      assume a ∈ y1 name ha => a ∈ y2 name hal proof iff.r (forall.e hy2 a) (iff.l (forall.e hy1 a) ha);
                      assume a ∈ y2 name ha => a ∈ y1 name har proof iff.r (forall.e hy1 a) (iff.l (forall.e hy2 a) ha);
                      => a ∈ y1 <-> a ∈ y2 name ha proof iff.i hal har;
                    }
                    => y1 = y2 name heq proof implies.e (forall.e (forall.e set_ext y1) y2) ha;
                  }
                }
                => unique y, forall b, b ∈ y <-> (exists a, a ∈ x and b = φ x a) name imageset_unique proof unique.i hex' heq;

                def  imageset :: forall b, b ∈ imageset <-> (exists a, a ∈ x and b = φ x a)
                name imageset_def proof imageset_unique;
              }

              // Axiom...
              assume (exists x, emptyset ∈ x and (forall a, a ∈ x -> pairset a (singletonset a) ∈ x))
              name   inductiveset_primitive {

                // Axiom...
                assume forall x, exists y, forall z, z ⊆ x -> z ∈ y
                name   powerset_primitive {

                  // A more useful form ("exactly" the power set...)
                  any x {
                    any y' assume forall z, z ⊆ x -> z ∈ y' name hy' {
                      def y := subset (_, a | a ⊆ x) y' name y_def;
                      any a {
                        => a ∈ y <-> a ∈ y' and a ⊆ x name lemma proof forall.e (iff.r (forall.e (forall.e (forallpred.e subset_def (_, a | a ⊆ x)) y') y) y_def) a;
                        assume a ∈ y name ha, any z assume z ∈ a name hz => z ∈ x name hal proof implies.e (forall.e (and.r (iff.l lemma ha)) z) hz;
                        assume a ⊆ x name ha, { => a ∈ y' name ha' proof implies.e (forall.e hy' a) ha; => a ∈ y name har proof iff.r lemma (and.i ha' ha); }
                        => a ∈ y <-> a ⊆ x name hiff proof iff.i hal har;
                      }
                      => exists y, forall a, a ∈ y <-> a ⊆ x name hex proof exists.i (exists y, forall a, a ∈ y <-> a ⊆ x) y hiff;
                    }
                    => exists y, forall a, a ∈ y <-> a ⊆ x name hex' proof exists.e (forall.e powerset_primitive x) hex (exists y, forall a, a ∈ y <-> a ⊆ x);
                    any y1 assume forall a, a ∈ y1 <-> a ⊆ x name hy1 {
                      any y2 assume forall a, a ∈ y2 <-> a ⊆ x name hy2 {
                        any a {
                          assume a ∈ y1 name ha => a ∈ y2 name hal proof iff.r (forall.e hy2 a) (iff.l (forall.e hy1 a) ha);
                          assume a ∈ y2 name ha => a ∈ y1 name har proof iff.r (forall.e hy1 a) (iff.l (forall.e hy2 a) ha);
                          => a ∈ y1 <-> a ∈ y2 name ha proof iff.i hal har;
                        }
                        => y1 = y2 name heq proof implies.e (forall.e (forall.e set_ext y1) y2) ha;
                      }
                    }
                    => unique y, forall a, a ∈ y <-> a ⊆ x name powerset_unique proof unique.i hex' heq;

                    def  powerset :: (forall a, a ∈ powerset <-> a ⊆ x)
                    name powerset_def proof powerset_unique;
                  }

                  // The axiom of choice (AC) is invoked (on the metatheoretic level!) when the `idef` keyword is used.
                  // `idef` is sufficient to prove the AC here:
                  any x assume emptyset ∉ x name hx {
                    any y assume y ∈ x name hy {
                      assume not (exists a, a ∈ y) name hy1 {
                        any a {
                          assume a ∈ y name ha => false name hf proof not.e hy1 (exists.i (exists a, a ∈ y) a ha);
                          => not a ∈ y name hy' proof not.i hf;
                        }
                        => y = emptyset name ye proof iff.l (forall.e emptyset_def y) hy';
                        => false name hf proof not.e hx (equals.e (□ | □ ∈ x) ye hy);
                      }
                      => exists a, a ∈ y name f_exists proof raa hf;
                      idef f :: f ∈ y name f_def proof f_exists;
                      #ls // f_def : (f ∈ y)
                    }
                    #ls // f_def : (forall y ∈ x, f y ∈ y)
                  }
                  // To complete the remaining steps, one could take the Cartesian product of x and ∪x, and use `subset` to make f_fn...
