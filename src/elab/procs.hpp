// Elab :: Procs

#ifndef PROCS_HPP_
#define PROCS_HPP_

#include <vector>
#include <utility>
#include <algorithm>
#include <tuple>
#include <optional>
#include <core.hpp>


// Some potentially useful proof procedures
namespace Elab::Procs {

  using std::vector;
  using std::pair, std::make_pair;
  using std::tuple, std::make_tuple, std::get;
  using std::optional, std::make_optional, std::nullopt;
  using namespace Core;


  // Pre: `e` is a propositional formula
  bool propValue(const Expr* e, const vector<bool>& fvmap);

  // Pre: `fvs.size()` <= 63
  template <typename F>
  inline void foreachValuation(const vector<unsigned int>& fvs, F f) {
    size_t n = fvs.size(), m = *std::max_element(fvs.cbegin(), fvs.cend()) + 1;
    uint64_t final = 1ull << n, mask = 0;
    do {
      vector<bool> fvmap(m);
      for (size_t i = 0; i < n; i++) if ((mask >> i) & 1u) fvmap[fvs[i]] = true;
      f(fvmap);
      mask++;
    } while (mask != final);
  }

  // Pre: `e` is arity-consistent
  // (Returns a copy in `pool`)
  // (Also removes IMPLIES, IFF and UNIQUE)
  Expr* toNNF(const Expr* e, const Context& ctx, Allocator<Expr>& pool, bool negated = false);

  // A substitution of undetermined variables with id in the interval [0, `ts.size()`).
  // `ts` should not contain circular dependencies. Use `nullptr` to represent unmodified variables.
  typedef vector<const Expr*> Subs;

  // See this for details.
  inline Expr* applySubs(const Expr* e, const Subs& subs, Allocator<Expr>& pool) {
    return e->updateVars(0, pool, [&subs, &pool] (unsigned int, Expr* x) {
      if (x->var.vartag == Expr::VarTag::UNDETERMINED && x->var.id < subs.size()) {
        const Expr* t = subs[x->var.id];
        if (t) return applySubs(t->clone(pool), subs, pool);
      }
      return x;
    });
  }

  // Returns (lgg, substitution to get l, substitution to get r).
  // Pre: { l, r } is arity-consistent
  tuple<Expr*, Subs, Subs> antiunify(const Expr* l, const Expr* r, Allocator<Expr>& pool);

  // All variables with `vartag == UNDETERMINED` are considered as undetermined first-order variables;
  //   others are just constants. Returns `nullopt` if unification failed.
  // Could take exponential time on certain cases.
  // Pre: the set of all expressions in `a` is arity-consistent
  optional<Subs> unify(vector<pair<const Expr*, const Expr*>> a, Allocator<Expr>& pool);

}

#endif // PROCS_HPP_
