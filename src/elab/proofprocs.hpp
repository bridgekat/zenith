// Elab :: Procs

#ifndef PROOFPROCS_HPP_
#define PROOFPROCS_HPP_

#include <vector>
#include <algorithm>
#include <core.hpp>


// Some potentially useful procedures
namespace Elab::Procs {

  using namespace Core;
  using std::vector;

  // Pre: `e` is a propositional formula
  bool propValue(const Expr* e, const vector<bool>& fvmap) {
    using enum Expr::Tag;
    switch (e->tag) {
      case VAR:
        if (!e->var.free) throw Unreachable();
        return e->var.id < fvmap.size() ? fvmap[e->var.id] : false;
      case TRUE:    return true;
      case FALSE:   return false;
      case NOT:     return !propValue(e->conn.l, fvmap);
      case AND:     return  propValue(e->conn.l, fvmap) && propValue(e->conn.r, fvmap);
      case OR:      return  propValue(e->conn.l, fvmap) || propValue(e->conn.r, fvmap);
      case IMPLIES: return !propValue(e->conn.l, fvmap) || propValue(e->conn.r, fvmap);
      case IFF:     return  propValue(e->conn.l, fvmap) == propValue(e->conn.r, fvmap);
      case FORALL: case EXISTS: case UNIQUE: case EMPTY: case FORALL2: case LAM:
        throw Unreachable();
    }
    throw NotImplemented();
  }

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
  Expr* toNNF(const Expr* e, const Context& ctx, Allocator<Expr>& pool, bool negated = false) {
    using enum Expr::Tag;
    switch (e->tag) {
      case VAR:
        return negated ? Expr::make(pool, NOT, e->clone(pool)) : e->clone(pool);
      case TRUE:
        return Expr::make(pool, negated ? FALSE : TRUE);
      case FALSE:
        return Expr::make(pool, negated ? TRUE : FALSE);
      case NOT:
        return toNNF(e->conn.l, ctx, pool, !negated);
      case AND:
        return Expr::make(pool, negated ? OR : AND,
          toNNF(e->conn.l, ctx, pool, negated),
          toNNF(e->conn.r, ctx, pool, negated));
      case OR:
        return Expr::make(pool, negated ? AND : OR,
          toNNF(e->conn.l, ctx, pool, negated),
          toNNF(e->conn.r, ctx, pool, negated));
      case IMPLIES:  // (p implies q) seen as ((not p) or q)
        return Expr::make(pool, negated ? AND : OR,
          toNNF(e->conn.l, ctx, pool, !negated),
          toNNF(e->conn.r, ctx, pool, negated));
      case IFF: {    // (p iff q) seen as ((p implies q) and (q implies p))
        Expr mp(IMPLIES, e->conn.l, e->conn.r);
        Expr mpr(IMPLIES, e->conn.r, e->conn.l);
        return Expr::make(pool, negated ? OR : AND,
          toNNF(&mp, ctx, pool, negated),
          toNNF(&mpr, ctx, pool, negated));
      }
      case FORALL:
        return Expr::make(pool, negated ? EXISTS : FORALL,
          e->bv, e->binder.arity, e->binder.sort,
          toNNF(e->binder.r, ctx, pool, negated));
      case EXISTS:
        return Expr::make(pool, negated ? FORALL : EXISTS,
          e->bv, e->binder.arity, e->binder.sort,
          toNNF(e->binder.r, ctx, pool, negated));
      case UNIQUE: { // (unique x, p) seen as ((exists x, p) and (forall x, p implies (forall x', p implies x = x')))
        Expr exi(EXISTS, e->bv, e->binder.arity, e->binder.sort, e->binder.r);
        Expr x(BOUND, 1), x_(BOUND, 0);
        Expr eq(FREE, ctx.eq, { &x, &x_ });
        Expr d(IMPLIES, e->binder.r, &eq);
        Expr c(FORALL, e->bv + "'", e->binder.arity, e->binder.sort, &d);
        Expr b(IMPLIES, e->binder.r, &c);
        Expr a(FORALL, e->bv, e->binder.arity, e->binder.sort, &b);
        Expr no2 = a;
        return Expr::make(pool, negated ? OR : AND,
          toNNF(&exi, ctx, pool, negated),
          toNNF(&no2, ctx, pool, negated));
      }
      case EMPTY: case FORALL2: case LAM:
        throw Unreachable();
    }
    throw NotImplemented();
  }



}

#endif // PROOFPROCS_HPP_
