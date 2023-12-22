// TODO: refactor

#ifndef APIMU_ELAB_TABLEAU_HPP
#define APIMU_ELAB_TABLEAU_HPP

#include <array>
#include <unordered_set>
#include <utility>
#include <vector>
#include "procs.hpp"

namespace apimu::elab {
#include "macros_open.hpp"

  using namespace core;

  // "Expression with hash" (a wrapper for `Expr const*` that overloads the `==` operator)
  struct ExprHash {
    Expr const* e;
    size_t hash;

    // `*e` should not be changed after this construction
    explicit ExprHash(Expr const* e) noexcept:
        e(e),
        hash(e->hash()) {}

    auto operator==(ExprHash const& r) const noexcept -> bool {
      return hash == r.hash && *e == *(r.e);
    }
    auto operator!=(ExprHash const& r) const noexcept -> bool {
      return hash != r.hash || *e != *(r.e);
    }

    struct GetHash {
      auto operator()(ExprHash const& eh) const noexcept -> size_t {
        return eh.hash;
      }
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
    enum Position : uint32_t { L, R };
    enum Type : uint32_t { Iota, Alpha, Beta, Gamma, GammaRetry, Delta, N };

    struct Branch {
      std::array<std::array<std::vector<Expr const*>, 2>, N> cedents;
      std::array<std::unordered_set<ExprHash, ExprHash::GetHash>, 2> hashset;
      std::array<std::array<size_t, 2>, N> indices;
      std::array<std::vector<bool>, 2> betaUsed;
      size_t depth, numUniversal;

      size_t numCedents;                                               // DEBUG CODE
      std::array<std::array<std::vector<size_t>, 2>, N> timestamps;    // DEBUG CODE
      std::array<std::array<std::vector<size_t>, 2>, N> numUniversals; // DEBUG CODE

      auto operator==(Branch const& r) const noexcept -> bool = default;
    };

    explicit Tableau(Context const& ctx) noexcept:
        ctx(ctx) {}

    auto addAntecedent(Expr const* e) -> void {
      auto const it = branch.hashset[L].insert(ExprHash(e));
      if (it.second) {
        auto const i = classify(L, e);
        branch.cedents[i][L].push_back(e);
        branch.timestamps[i][L].push_back(branch.numCedents++);
        branch.numUniversals[i][L].push_back(0);
        if (i == Beta)
          branch.betaUsed[L].push_back(false);
      }
    }

    auto addSuccedent(Expr const* e) -> void {
      auto const it = branch.hashset[R].insert(ExprHash(e));
      if (it.second) {
        auto const i = classify(R, e);
        branch.cedents[i][R].push_back(e);
        branch.timestamps[i][R].push_back(branch.numCedents++);
        branch.numUniversals[i][R].push_back(0);
        if (i == Beta)
          branch.betaUsed[R].push_back(false);
      }
    }

    // TODO: initial check (the given proof state may already be closed)

    auto clear() noexcept -> void {
      pools.clear();
      pools.emplace_back();
      for (auto i = uint32_t{0}; i < N; i++) {
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

    auto search(size_t setMaxDepth, size_t setMaxTabDepth) -> bool;
    auto iterativeDeepening(size_t setMaxTabDepth, size_t step) -> bool;
    auto printState() -> std::string;
    auto printStateDebug() -> std::string;
    auto printStats() -> std::string;

  private:
    std::vector<Allocator<Expr>> pools;
    Context const& ctx;

    Branch branch = Branch{}; // Current branch

    // Ephemeral states
    std::vector<Branch> cont; // Other branches (to the right of current)
    size_t numSkolem = 0;
    size_t maxDepth = 0;
    size_t maxTabDepth = 0;

    // Statistics
    size_t maxDepthReached = 0;
    size_t invocations = 0;
    size_t branches = 0;
    size_t backtrackPoints = 0;

    friend class WithCedent;

    static auto invert(Position pos) noexcept -> Position {
      return (pos == L) ? R : L;
    };
    static auto classify(Position antesucc, Expr const* e) noexcept -> Type;
    auto applySubs(procs::Subs const& subs, bool assertNoChange) -> void;
    auto dfs(size_t depth) -> bool;

    auto checkBranch(Branch const& b) -> void;
    auto check() -> void;
    auto debughtml(std::string const& filename) -> void;
  };

#include "macros_close.hpp"
}

#endif // APIMU_ELAB_TABLEAU_HPP
