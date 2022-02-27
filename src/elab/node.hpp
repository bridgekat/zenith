// Elab :: Node

#ifndef NODE_HPP_
#define NODE_HPP_

#include <core.hpp>

namespace Elab {

  // An alternative representation for Fitch-style natural deduction proofs, designed to be more
  // conveniently handled by automated proving procedures. This includes most constructs supported
  // by ApiMu, except definitions.
  // - Can be understood as a rooted, ordered tree structure (tree edges represent context changes)
  //   with extra links among leaf nodes (theorem references) such that every link goes from right to left.
  // - A cross-link (u, v) involves two transformations: from v to LCA(u, v) context-changing introduction
  //   rules are applied; from LCA(u, v) to u the weakening rule is implicitly applied.
  class Node {
  public:

  };
  
}

#endif // NODE_HPP_

