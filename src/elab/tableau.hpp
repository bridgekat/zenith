// Elab :: Tableau

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


  // "Expression with hash" (a wrapper for `const Expr*` that overloads the `==` operator)
  struct ExprHash {
    const Expr* e;
    size_t hash;

    // `*e` should not be changed after this construction
    explicit ExprHash(const Expr* e): e(e), hash(e->hash()) {}
    bool operator==(const ExprHash& r) const { return hash == r.hash && *e == *(r.e); }
    bool operator!=(const ExprHash& r) const { return hash != r.hash || *e != *(r.e); }

    struct GetHash {
      size_t operator()(const ExprHash& eh) const { return eh.hash; }
    };
  };

  // Method of analytic tableaux (aka. sequent calculus) for classical logic

  // For an introduction, see:
  // - https://en.wikipedia.org/wiki/Method_of_analytic_tableaux
  // - https://en.wikipedia.org/wiki/Sequent_calculus#The_system_LK

  // For implementation-related things, see:
  // - https://www21.in.tum.de/teaching/sar/SS20/2.pdf
  // - https://moodle.risc.jku.at/pluginfile.php/10562/mod_resource/content/12/07-fol3.pdf
  // - https://www.wolfgangschwarz.net/trees/
  // - https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.216.388&rep=rep1&type=pdf
  //   (Also contains several completeness proofs)

  class Tableau {
  public:

    const Context& ctx;
    // Antecedents in `cedents[0]` and `hashset[0]`
    // Succedents in `cedents[1]` and `hashset[1]`
    vector<const Expr*> cedents[2];                        // For a queue-like structure
    unordered_set<ExprHash, ExprHash::GetHash> hashset[2]; // For fast membership testing

    Tableau(const Context& ctx): ctx(ctx), cedents(), hashset() {}

    void addAntecedent(const Expr* e) {
      auto it = hashset[0].insert(ExprHash(e));
      if (it.second) cedents[0].push_back(e);
    }

    void addSuccedent(const Expr* e) {
      auto it = hashset[1].insert(ExprHash(e));
      if (it.second) cedents[1].push_back(e);
    }

    // TODO: initial check (the given proof state may already be closed)

    void clear() {
      hashset[0].clear();
      cedents[0].clear();
      hashset[1].clear();
      cedents[1].clear();
    }

    // Pre: all elements of `ante`, `succ`, `anteSet` and `succSet` are valid, well-formed formulas
    // All states will be unmodified/restored
    bool dfs(size_t antei, size_t succi);
  };

}

#endif // TABLEAU_HPP_
