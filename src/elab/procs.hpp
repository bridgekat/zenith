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
  using std::tuple, std::make_tuple;
  using std::optional, std::make_optional, std::nullopt;
  using namespace Core;


  // Pre: `e` is a propositional formula
  bool propValue(const Expr* e, const vector<bool>& fvmap);

  // Pre: `fvs.size()` <= 63
  template <typename F>
  void foreachValuation(const vector<unsigned int>& fvs, F f) {
    size_t n = fvs.size(), m = *std::max_element(fvs.cbegin(), fvs.cend()) + 1;
    uint64_t final = 1ull << n, mask = 0;
    do {
      vector<bool> fvmap(m);
      for (size_t i = 0; i < n; i++) if ((mask >> i) & 1u) fvmap[fvs[i]] = true;
      f(fvmap);
      mask++;
    } while (mask != final);
  }

  // Pre: `e` is well-formed
  // (Returns a copy in `pool`)
  // (Also removes IMPLIES, IFF and UNIQUE)
  Expr* toNNF(const Expr* e, const Context& ctx, Allocator<Expr>& pool, bool negated = false);

  // A substitution of free variables with id in the interval [`offset`, `offset + ts.size()`).
  struct Subs {
    unsigned int offset;
    vector<const Expr*> ts;
  };

  // See this for details.
  Expr* applySubs(const Expr* e, const Subs& subs, Allocator<Expr>& pool) {
    return e->updateVars(0, pool, [o = subs.offset, &subs, &pool] (unsigned int n, Expr* x) {
      if (x->var.free && x->var.id >= o && x->var.id < o + subs.ts.size()) {
        return subs.ts[x->var.id - o]->clone(pool);
      }
      return x;
    });
  }

  // All free variables with `id >= offset` are considered as undetermined variables; others are just constants.
  // Returns `nullopt` if unification failed.
  optional<Subs> unify(unsigned int offset, vector<pair<const Expr*, const Expr*>> a, Allocator<Expr>& pool);

  // Returns (lgg, substitution to get l, substitution to get r).
  tuple<Expr*, Subs, Subs> antiunify(unsigned int offset, const Expr* l, const Expr* r, Allocator<Expr>& pool);

}

#endif // PROCS_HPP_
