#ifndef APIMU_ELAB_PROCS_HPP
#define APIMU_ELAB_PROCS_HPP

#include <algorithm>
#include <optional>
#include <tuple>
#include <utility>
#include <vector>
#include <core/expr.hpp>
#include <core/fol/fol.hpp>

// Some potentially useful syntactic operations
namespace apimu::elab::procs {
#include "macros_open.hpp"

  using namespace core;

  // Pre (checked): `e` is a propositional formula
  auto propValue(Expr const* e, std::vector<bool> const& fvmap) -> bool;

  // Pre: `fvs.size()` < 64
  template <typename F>
  inline auto foreachValuation(std::vector<uint64_t> const& fvs, F f) -> void {
    auto const n = fvs.size();
    auto const m = *std::max_element(fvs.cbegin(), fvs.cend()) + 1;
    auto const final = 1_z << n;
    auto mask = 0_z;
    do {
      auto fvmap = std::vector<bool>(m);
      for (auto i = 0_z; i < n; i++)
        if ((mask >> i) & 1u) fvmap[fvs[i]] = true;
      f(fvmap);
      mask++;
    } while (mask != final);
  }

  // Returns { VFree, skolem } applied to a number of meta-variables ("implicitly universally quantified" variables)
  inline auto makeSkolem(uint64_t skolem, std::vector<uint64_t> const& metas, Allocator<Expr>& pool) -> Expr const* {
    auto res = pool.make(Expr::VFree, skolem);
    for (auto const i: metas) res = pool.make(res, pool.make(Expr::VMeta, i));
    return res;
  }

  // Returns the negation normal form of a first-order formula (lifetime bounded by `e` and `pool`).
  // Also removes "implies", "iff" and "unique".
  // Non-first-order formulas will not be changed.
  auto nnf(Expr const* e, Allocator<Expr>& pool, bool negated = false) -> Expr const*;

  // Returns the Skolem normal form of a first-order formula (lifetime bounded by `e` and `pool`).
  // `meta` and `skolem` denote the first available meta- and free-variable ID, respectively.
  // `metas` denotes the list of universally quantified variables currently in scope (will not be changed).
  // Negations are pushed in (by calling `nnf` as needed). Non-first-order formulas will not be changed.
  auto skolemize(Expr const* e, uint64_t& meta, uint64_t& skolem, std::vector<uint64_t>& metas, Allocator<Expr>& pool)
    -> Expr const*;

  // This variant uses 0 and `ctx.size()` as the first available meta- and free-variable ID (the most common choice).
  inline auto skolemize(Expr const* e, Context const& ctx, Allocator<Expr>& pool) -> Expr const* {
    auto meta = uint64_t{0}, skolem = static_cast<uint64_t>(ctx.size());
    auto metas = std::vector<uint64_t>();
    return skolemize(e, meta, skolem, metas, pool);
  }

  // Returns the conjunctive normal form (in the form of clauses) of a first-order formula **already in Skolem normal
  // form**. (Propositional formulas are already in Skolem normal form; no Skolemization is needed in this case.)
  // Non-first-order formulas, "not", "implies", "iff", "forall", "exists" and "unique" **will not be further
  // splitted**.
  auto cnf(Expr const* e, Allocator<Expr>& pool) -> std::vector<std::vector<Expr const*>>;

  // Show a set of clauses
  auto showClauses(std::vector<std::vector<Expr const*>> const& cs, Context const& ctx) -> std::string;

  // Collect a set of clauses to a formula
  // Expr const* collectClauses(vector<vector<Expr const*>> const& cs, Allocator<Expr>& pool);

  // A substitution of meta-variables with id in the interval [0, `ts.size()`).
  // `ts` should not contain circular dependencies. Use `nullptr` to represent unmodified variables.
  using Subs = std::vector<Expr const*>;

  // See this for details.
  inline auto applySubs(Expr const* e, Subs const& subs, Allocator<Expr>& pool) -> Expr const* {
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
  auto showSubs(Subs const& subs, Context const& ctx) -> std::string;

  // Check if two expressions are syntactically equal (up to alpha-renaming) after applying a substitution.
  // Probably faster than simply apply and check...
  auto equalAfterSubs(Expr const* lhs, Expr const* rhs, Subs const& subs) -> bool;

  // First-order (syntactical) anti-unification.
  // Returns { lgg, substitution to get lhs, substitution to get rhs }.
  auto antiunify(Expr const* lhs, Expr const* rhs, Allocator<Expr>& pool) -> std::tuple<Expr const*, Subs, Subs>;

  // First-order (syntactical) unification.
  // All variables with `var.tag == VMeta` are considered as undetermined variables; others are just constants.
  // Returns { mgu }, or `nullopt` if mgu does not exist.
  // Could take exponential time on certain cases.
  auto unify(std::vector<std::pair<Expr const*, Expr const*>> eqs, Allocator<Expr>& pool) -> std::optional<Subs>;

  // TODO: Huet's higher-order unification, E-unification, etc.
#include "macros_close.hpp"
}

#endif // APIMU_ELAB_PROCS_HPP
