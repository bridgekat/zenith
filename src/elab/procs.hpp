// Elab :: Procs

#ifndef PROCS_HPP_
#define PROCS_HPP_

#include <algorithm>
#include <optional>
#include <tuple>
#include <utility>
#include <vector>
#include <core/expr.hpp>
#include <core/fol/fol.hpp>

// Some potentially useful syntactic operations
namespace Elab::Procs {

  using std::string;
  using std::vector;
  using std::pair, std::make_pair;
  using std::tuple, std::make_tuple, std::get;
  using std::optional, std::make_optional, std::nullopt;
  using namespace Core;

  // Pre (checked): `e` is a propositional formula
  bool propValue(Expr const* e, vector<bool> const& fvmap) noexcept;

  // Pre: `fvs.size()` < 64
  template <typename F>
  inline void foreachValuation(vector<uint64_t> const& fvs, F f) {
    size_t n = fvs.size(), m = *std::max_element(fvs.cbegin(), fvs.cend()) + 1;
    uint64_t final = 1ull << n, mask = 0;
    do {
      vector<bool> fvmap(m);
      for (size_t i = 0; i < n; i++)
        if ((mask >> i) & 1u) fvmap[fvs[i]] = true;
      f(fvmap);
      mask++;
    } while (mask != final);
  }

  // Returns { VFree, skolem } applied to a number of meta-variables ("implicitly universally quantified" variables)
  inline Expr const* makeSkolem(uint64_t skolem, vector<uint64_t> const& metas, Allocator<Expr>& pool) {
    Expr const* res = pool.emplace(Expr::VFree, skolem);
    for (uint64_t i: metas) res = pool.emplace(res, pool.emplace(Expr::VMeta, i));
    return res;
  }

  // Returns the negation normal form of a first-order formula (lifetime bounded by `e` and `pool`).
  // Also removes "implies", "iff" and "unique".
  // Non-first-order formulas will not be changed.
  Expr const* nnf(Expr const* e, Allocator<Expr>& pool, bool negated = false);

  // Returns the Skolem normal form of a first-order formula (lifetime bounded by `e` and `pool`).
  // `meta` and `skolem` denote the first available meta- and free-variable ID, respectively.
  // `metas` denotes the list of universally quantified variables currently in scope (will not be changed).
  // Negations are pushed in (by calling `nnf` as needed). Non-first-order formulas will not be changed.
  Expr const*
  skolemize(Expr const* e, uint64_t& meta, uint64_t& skolem, vector<uint64_t>& metas, Allocator<Expr>& pool);
  // This variant uses 0 and `ctx.size()` as the first available meta- and free-variable ID (the most common choice).
  inline Expr const* skolemize(Expr const* e, Context const& ctx, Allocator<Expr>& pool) {
    uint64_t meta = 0, skolem = ctx.size();
    vector<uint64_t> metas;
    return skolemize(e, meta, skolem, metas, pool);
  }

  // Returns the conjunctive normal form (in the form of clauses) of a first-order formula **already in Skolem normal
  // form**. (Propositional formulas are already in Skolem normal form; no Skolemization is needed in this case.)
  // Non-first-order formulas, "not", "implies", "iff", "forall", "exists" and "unique" **will not be further
  // splitted**.
  vector<vector<Expr const*>> cnf(Expr const* e, Allocator<Expr>& pool);

  // Show a set of clauses
  string showClauses(vector<vector<Expr const*>> const& cs, Context const& ctx);

  // Collect a set of clauses to a formula
  // Expr const* collectClauses(vector<vector<Expr const*>> const& cs, Allocator<Expr>& pool);

  // A substitution of meta-variables with id in the interval [0, `ts.size()`).
  // `ts` should not contain circular dependencies. Use `nullptr` to represent unmodified variables.
  using Subs = vector<Expr const*>;

  // See this for details.
  inline Expr const* applySubs(Expr const* e, Subs const& subs, Allocator<Expr>& pool) {
    return e->updateVars(
      [&subs, &pool](uint64_t, Expr const* x) {
        return (x->var.tag == Expr::VMeta && x->var.id < subs.size() && subs[x->var.id])
               ? applySubs(subs[x->var.id], subs, pool)
               : x;
      },
      pool
    );
  }

  // Show a substitution
  string showSubs(Subs const& subs, Context const& ctx);

  // Check if two expressions are syntactically equal (up to alpha-renaming) after applying a substitution.
  // Probably faster than simply apply and check...
  bool equalAfterSubs(Expr const* lhs, Expr const* rhs, Subs const& subs) noexcept;

  // First-order (syntactical) anti-unification.
  // Returns { lgg, substitution to get lhs, substitution to get rhs }.
  tuple<Expr const*, Subs, Subs> antiunify(Expr const* lhs, Expr const* rhs, Allocator<Expr>& pool);

  // First-order (syntactical) unification.
  // All variables with `var.tag == VMeta` are considered as undetermined variables; others are just constants.
  // Returns { mgu }, or `nullopt` if mgu does not exist.
  // Could take exponential time on certain cases.
  optional<Subs> unify(vector<pair<Expr const*, Expr const*>> eqs, Allocator<Expr>& pool);

  // TODO: Huet's higher-order unification, E-unification, etc.

}

#endif // PROCS_HPP_
