// Elab :: Tableau

// TODO: refactor

#ifndef TABLEAU_HPP_
#define TABLEAU_HPP_

#include <unordered_set>
#include <utility>
#include <vector>
#include <core.hpp>
#include "procs.hpp"

namespace Elab {

  using std::string;
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
    // Cedents are classified as either "ι" (atomic), "α" (non-branching), "β" (branching), "γ" (universal) or "δ"
    // (existential). (TODO: "ε" (equational) and "φ" (second-order universal))
    enum Position : unsigned int { L, R };
    enum Type : unsigned int { Iota, Alpha, Beta, Gamma, GammaRe, Delta, N };

    struct Branch {
      vector<const Expr*> cedents[N][2];
      unordered_set<ExprHash, ExprHash::GetHash> hashset[2];
      size_t indices[N][2];
      vector<bool> betaUsed[2];
      size_t depth, numUniversal;

      size_t numCedents;                  // DEBUG CODE
      vector<size_t> timestamps[N][2];    // DEBUG CODE
      vector<size_t> numUniversals[N][2]; // DEBUG CODE

      bool operator==(const Branch& r) const noexcept = default;
    };

    Tableau(const Context& ctx) noexcept: pools(), ctx(ctx), branch{}, cont(), numSkolem{}, maxDepth{}, maxTabDepth{} {}

    void addAntecedent(const Expr* e) {
      auto it = branch.hashset[L].insert(ExprHash(e));
      if (it.second) {
        unsigned int i = classify(L, e);
        branch.cedents[i][L].push_back(e);
        branch.timestamps[i][L].push_back(branch.numCedents++);
        branch.numUniversals[i][L].push_back(0);
        if (i == Beta) branch.betaUsed[L].push_back(false);
      }
    }

    void addSuccedent(const Expr* e) {
      auto it = branch.hashset[R].insert(ExprHash(e));
      if (it.second) {
        unsigned int i = classify(R, e);
        branch.cedents[i][R].push_back(e);
        branch.timestamps[i][R].push_back(branch.numCedents++);
        branch.numUniversals[i][R].push_back(0);
        if (i == Beta) branch.betaUsed[R].push_back(false);
      }
    }

    // TODO: initial check (the given proof state may already be closed)

    void clear() noexcept {
      pools.clear();
      pools.emplace_back();
      for (unsigned int i = 0; i < N; i++) {
        branch.cedents[i][L].clear();
        branch.cedents[i][R].clear();
        branch.indices[i][L] = 0;
        branch.indices[i][R] = 0;
        branch.timestamps[i][L].clear();
        branch.timestamps[i][R].clear();
        branch.numUniversals[i][L].clear();
        branch.numUniversals[i][R].clear();
      }
      branch.hashset[L].clear();
      branch.hashset[R].clear();
      branch.betaUsed[L].clear();
      branch.betaUsed[R].clear();
      branch.depth = 0;
      branch.numUniversal = 0;
      branch.numCedents = 0;
    }

    bool search(size_t maxDepth, size_t maxTabDepth);
    bool iterativeDeepening(size_t maxTabDepth, size_t step);
    string printState();
    string printStateDebug();
    string printStats();

  private:
    vector<Allocator<Expr>> pools;
    const Context& ctx;

    Branch branch; // Current branch

    // Ephemeral states
    vector<Branch> cont; // Other branches (to the right of current)
    size_t numSkolem, maxDepth, maxTabDepth;

    // Statistics
    size_t maxDepthReached = 0, invocations = 0, branches = 0, backtrackPoints = 0;

    friend class WithCedent;

    static Position invert(Position pos) noexcept { return (pos == L) ? R : L; };
    static Type classify(Position antesucc, const Expr* e) noexcept;
    void applySubs(const Procs::Subs& subs, bool assertNoChange);
    bool dfs(size_t depth);

    void checkBranch(const Branch& b);
    void check();
    void debughtml(const string& filename);
  };

}

#endif // TABLEAU_HPP_
