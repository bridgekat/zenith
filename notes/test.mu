#ai none // Unifies with given premises only
any x y z {
  assume (x = y) (y = z) name h1 h2 {
    (x = z) name h by eq.trans h1 h2;
  }
  #ls // h : (x = y -> y = z -> x = z)
}
#ls // h : (forall x y z, x = y -> y = z -> x = z)

#ai local // Try to unify with everything currently in context! No names are required in principle.
any x y z {
  assume (x = y) (y = z) {
    (x = z) by eq.trans;
    (x = z) by "transitivity of equality"; // Use of complex names is also supported
  }
  #ls // ? : (x = y -> y = z -> x = z)
}
#ls // ? : (forall x y z, x = y -> y = z -> x = z)

#ai alpha_turnstile_zero // Neural networks activated! If you take small steps, there is no need to explicitly state the rules.
any x y z {
  assume (x = y) (y = z) {
    (x = z);
  }
  #ls // ? : (x = y -> y = z -> x = z)
}
#ls // ? : (forall x y z, x = y -> y = z -> x = z)

// Extension by definitions...
any x y {
  def phi :<-> (x = y and y = x) name phi_def;
  #ls // phi_def : (phi <-> (x = y and y = x))
}
#ls // phi_def : (forall x y, phi <-> (x = y and y = x))

undef phi;
#ls // (phi and phi_def vanish)

// Alternatively...
any x y def phi :<-> (x = y and y = x) name phi_def;
undef phi;

// One may as well define metavariables...
any x y mform r; // r denotes arbitrary binary relation

assume (forall x, r x x) (forall x y, r x y -> r y x -> x = y) (forall x y z, r x y -> r y z -> r x z) {
  // Assume r is a partial order...
  any x y z assume (r x y) (r y z) (r z x) {
    (x = y);
    (x = z);
    (y = z);
  }
}
#ls // Now you have results about r...
// You can substitute in any formula in the place of r! (Just like forall.e)

undef r;


// Partial functions!
any x y assume (x = y) {
  def f := (x + y) name f_def;
  #ls // f_def : f = x + y
}
#ls // f_def : (forall x y, x = y -> f = x + y)
undef f;




