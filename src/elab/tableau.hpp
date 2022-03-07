// Elab :: Tableau

#ifndef TABLEAU_HPP_
#define TABLEAU_HPP_

#include <vector>
#include <utility>
#include <unordered_set>
#include <core.hpp>
#include "procs.hpp"


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
    explicit ExprHash(const Expr* e) noexcept: e(e), hash(e->hash()) {}
    bool operator==(const ExprHash& r) const noexcept { return hash == r.hash && *e == *(r.e); }
    bool operator!=(const ExprHash& r) const noexcept { return hash != r.hash || *e != *(r.e); }

    struct GetHash {
      size_t operator()(const ExprHash& eh) const noexcept { return eh.hash; }
    };
  };

  // Method of analytic tableaux (aka. sequent calculus) for classical logic
  // (LOTS OF TEMPORARY CODE NOW!)

  // For an introduction, see:
  // - https://en.wikipedia.org/wiki/Method_of_analytic_tableaux
  // - https://en.wikipedia.org/wiki/Sequent_calculus#The_system_LK
  // - https://www.wolfgangschwarz.net/trees/
  //   (Also contains implementation tips)

  // For implementation-related things, see:
  // - https://www21.in.tum.de/teaching/sar/SS20/2.pdf
  // - https://moodle.risc.jku.at/pluginfile.php/10562/mod_resource/content/12/07-fol3.pdf
  //   (Free-variable tableau, but uses backtracking...)
  // - https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.216.388&rep=rep1&type=pdf
  //   (Also contains several completeness proofs)
  // - https://publikationen.bibliothek.kit.edu/4572003/3209
  //   (Free-variable tableau without backtracking!)

  // For translation of LK (tableaux) to NK (natural deduction), see:
  // - http://ceur-ws.org/Vol-2162/paper-03.pdf

  class Tableau {
  public:
    // Antecedents in `cedents[...][L]` and `hashset[L]`
    // Succedents in `cedents[...][R]` and `hashset[R]`
    // Cedents are classified as either "ι" (atomic), "α" (non-branching), "β" (branching), "γ" (universal) or "δ" (existential).
    // (TODO: "ε" (equational) and "φ" (second-order universal))
    enum Position: unsigned int { L, R };
    enum Type: unsigned int { ι, α, β, γ, γre, δ, N }; // Tweak parameters here (1/3)

    struct Branch {
      vector<const Expr*> cedents[N][2];
      unordered_set<ExprHash, ExprHash::GetHash> hashset[2];
      size_t indices[N][2];
      size_t numUniversalAbove;
    };

    Tableau(const Context& ctx) noexcept:
      pools(), ctx(ctx), branch{}, cont(), numUniversal{}, numSkolem{}, maxDepth{} {}

    void addAntecedent(const Expr* e) {
      auto it = branch.hashset[L].insert(ExprHash(e));
      if (it.second) branch.cedents[classify(L, e)][L].push_back(e);
    }

    void addSuccedent(const Expr* e) {
      auto it = branch.hashset[R].insert(ExprHash(e));
      if (it.second) branch.cedents[classify(R, e)][R].push_back(e);
    }

    // TODO: initial check (the given proof state may already be closed)

    void clear() noexcept {
      pools.clear();
      pools.emplace_back();
      for (unsigned int i = 0; i < N; i++) {
        branch.cedents[i][L].clear();
        branch.cedents[i][R].clear();
      }
      branch.hashset[L].clear();
      branch.hashset[R].clear();
    }

    bool search(size_t maxDepth);
    bool iterativeDeepening(size_t maxDepth, size_t step);
    string printState();
    string printStateDebug();
    string printStats();

  private:
    vector<Allocator<Expr>> pools;
    const Context& ctx;

    Branch branch; // Current branch
    vector<Branch> cont;
    size_t numUniversal, numSkolem, maxDepth;

    // Statistics
    size_t maxDepthReached = 0, invocations = 0, branches = 0, backtrackPoints = 0;

    friend class WithCedent;

    static Position invert(Position pos) noexcept { return (pos == L)? R : L; };
    static Type classify(Position antesucc, const Expr* e) noexcept;
    bool applySubs(const Procs::Subs& subs);
    bool dfs(size_t depth);
  };

}

#endif // TABLEAU_HPP_
