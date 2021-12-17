/*
--------------------------------------------------------------------------------
This file contains the definitions and axioms from the ZFC set theory.
Though written in a formal syntax, this file is informal (i.e. NOT verified by a computer)!

17/12/2021
--------------------------------------------------------------------------------
*/


#ai local search_simple smt_z5 gpt10f alpha_turnstile_zero
// Activate some of the inference engines I downloaded from the future world


mterm emptyset;
any x y mform in;

notation ∅ := emptyset;
infix ∈ := in, allow_forall_exists 0;
// We can write "forall a ∈ x, ..." to mean "forall a, a ∈ x -> ..."
//     or write "exists a ∈ x, ..." to mean "exists a, a ∈ x and ..."

assume (forall x y, (forall z, z ∈ x <-> z ∈ y) -> x = y)
  name ax_ext
 alias "Axiom of extensionality"
       "Set extensionality"
       "Sets which have the same elements are equal"
{

assume (forall x, (exists a ∈ x) -> (exists y ∈ x, not exists z, z ∈ x and z ∈ y))
  name ax_regular
 alias "Axiom of regularity"
       "Axiom of foundation"
       "Every non-empty set x contains a member y such that x and y are disjoint sets"
{




