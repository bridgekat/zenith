// Elab :: Procs

#ifndef PROCS_HPP_
#define PROCS_HPP_

#include <vector>
#include <utility>
#include <algorithm>
#include <tuple>
#include <optional>
#include <core.hpp>


// Some potentially useful syntactic operations
namespace Elab::Procs {

  using std::string;
  using std::vector;
  using std::pair, std::make_pair;
  using std::tuple, std::make_tuple, std::get;
  using std::optional, std::make_optional, std::nullopt;
  using namespace Core;


  // Pre (checked): `e` is a propositional formula
  bool propValue(const Expr* e, const vector<bool>& fvmap) noexcept;

  // Pre: `fvs.size()` < 64
  template <typename F>
  inline void foreachValuation(const vector<uint64_t>& fvs, F f) {
    size_t n = fvs.size(), m = *std::max_element(fvs.cbegin(), fvs.cend()) + 1;
    uint64_t final = 1ull << n, mask = 0;
    do {
      vector<bool> fvmap(m);
      for (size_t i = 0; i < n; i++) if ((mask >> i) & 1u) fvmap[fvs[i]] = true;
      f(fvmap);
      mask++;
    } while (mask != final);
  }

  // Returns { VFree, skolem } applied to a number of meta-variables ("implicitly universally quantified" variables)
  inline const Expr* makeSkolem(uint64_t meta, uint64_t skolem, Allocator<Expr>& pool) {
    const Expr* res = pool.emplaceBack(Expr::VFree, skolem);
    for (uint64_t i = 0; i < meta; i++) res = pool.emplaceBack(res, pool.emplaceBack(Expr::VMeta, i));
    return res;
  }

  // Returns the negation normal form of a first-order formula (lifetime bounded by `e` and `pool`).
  // Also removes "implies", "iff" and "unique".
  // Non-first-order formulas will not be changed.
  const Expr* nnf(const Expr* e, Allocator<Expr>& pool, bool negated = false);

  // Returns the conjunctive normal form (in the form of clauses) of a first-order formula **already in negation normal form**.
  // Also does Skolemization (`meta` and `skolem` denote the first available meta- and free-variable ID, respectively).
  // Non-first-order formulas, "not", "implies", "iff" and "unique" will not be further splitted.
  vector<vector<const Expr*>> cnf(const Expr* e, uint64_t meta, uint64_t skolem, Allocator<Expr>& pool);

  // Show a set of clauses
  string showClauses(const vector<vector<const Expr*>>& cs, const Context& ctx);

  // A substitution of meta-variables with id in the interval [0, `ts.size()`).
  // `ts` should not contain circular dependencies. Use `nullptr` to represent unmodified variables.
  using Subs = vector<const Expr*>;

  // See this for details.
  inline const Expr* applySubs(const Expr* e, const Subs& subs, Allocator<Expr>& pool) {
    return e->updateVars([&subs, &pool] (uint64_t, const Expr* x) {
      return (x->var.tag == Expr::VMeta && x->var.id < subs.size() && subs[x->var.id]) ?
              applySubs(subs[x->var.id], subs, pool) : x;
    }, pool);
  }

  // Show a substitution
  string showSubs(const Subs& subs, const Context& ctx);

  // Check if two expressions are syntactically equal (up to alpha-renaming) after applying a substitution.
  // Probably faster than simply apply and check...
  bool equalAfterSubs(const Expr* lhs, const Expr* rhs, const Subs& subs) noexcept;

  // First-order (syntactical) anti-unification.
  // Returns { lgg, substitution to get lhs, substitution to get rhs }.
  tuple<const Expr*, Subs, Subs> antiunify(const Expr* lhs, const Expr* rhs, Allocator<Expr>& pool);

  // First-order (syntactical) unification.
  // All variables with `var.tag == VMeta` are considered as undetermined variables; others are just constants.
  // Returns { mgu }, or `nullopt` if mgu does not exist.
  // Could take exponential time on certain cases.
  optional<Subs> unify(vector<pair<const Expr*, const Expr*>> eqs, Allocator<Expr>& pool);

  // TODO: Huet's higher-order unification, E-unification, etc.

}

#endif // PROCS_HPP_
