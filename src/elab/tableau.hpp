// Elab :: TableauSearch

#ifndef TABLEAU_HPP_
#define TABLEAU_HPP_

#include <vector>
#include <utility>
#include <unordered_set>
#include <core.hpp>


namespace Elab {

  using std::vector;
  using std::pair, std::make_pair;
  using std::unordered_set;
  using namespace Core;


  // Method of analytic tableaux (aka. sequent calculus) for classical logic
  // See: https://en.wikipedia.org/wiki/Method_of_analytic_tableaux
  // See: https://en.wikipedia.org/wiki/Sequent_calculus#The_system_LK
  class TableauSearch {
  public:
    // Current state (antecedents and succedents)
    vector<const Expr*> ante, succ;
    // Current indices
    size_t antei, succi;

    // Expression wrapper (with overloaded equality and hash function)
    struct ExprEq {
      const Expr* e;
      bool operator=(const ExprEq& r) const { return *e == *(r.e); }
      // TODO
    };
    // Hash sets
    unordered_set<ExprEq> antehs, succhs;

    // Main DFS subroutine
    // Invariant: all states will be unmodified/restored
    void dfs() {
      // If succedents have not been exhausted, we break them down first
      // (There should be a relatively small number of them, compared to antecedents!)
      if (succi < succ.size()) {

        return;
      }
      // Otherwise we break down one antecedent
      if (antei < ante.size()) {

        return;
      }
      // We have used up all non-branching rules!
      
    }
  };

}

#endif // TABLEAU_HPP_
