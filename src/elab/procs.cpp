#include "procs.hpp"

namespace Elab::Procs {

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

  Expr* toNNF(const Expr* e, const Context& ctx, Allocator<Expr>& pool, bool negated) {
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

  // A simple anti-unification algorithm.
  // See: https://en.wikipedia.org/wiki/Anti-unification_(computer_science)#First-order_syntactical_anti-unification
  class Antiunifier {
  public:
    unsigned int nextid;
    Allocator<Expr>* pool;
    Subs ls, rs;

    Antiunifier(): nextid{}, pool{}, ls{}, rs{} {}
    Antiunifier(const Antiunifier&) = delete;
    Antiunifier& operator=(const Antiunifier&) = delete;

    Expr* dfs(const Expr* lhs, const Expr* rhs) {
      using enum Expr::Tag;

      // If roots are different, return this
      auto different = [this, lhs, rhs] () {
        unsigned int id = nextid;
        nextid++;
        ls.ts.push_back(lhs);
        rs.ts.push_back(rhs);
        return Expr::make(*pool, FREE, id);
      };
 
      if (lhs->tag != rhs->tag) return different();
      // lhs->tag == rhs->tag
      switch (lhs->tag) {
        case EMPTY:
          throw Unreachable();
        case VAR: {
          if (lhs->var.free != rhs->var.free || lhs->var.id != rhs->var.id) {
            return different();
          }
          Expr* res = Expr::make(*pool, lhs->var.free, lhs->var.id), * last = nullptr;
          const Expr* plhs = lhs->var.c, * prhs = rhs->var.c;
          for (; plhs && prhs; plhs = plhs->s, prhs = prhs->s) {
            Expr* q = dfs(plhs, prhs);
            (last? last->s : res->var.c) = q;
            last = q;
          }
          (last? last->s : res->var.c) = nullptr;
          if (plhs || prhs) throw Unreachable();
          return res;
        }
        case TRUE: case FALSE:
          return Expr::make(*pool, lhs->tag);
        case NOT:
          return Expr::make(*pool, lhs->tag, dfs(lhs->conn.l, rhs->conn.l));
        case AND: case OR: case IMPLIES: case IFF:
          return Expr::make(*pool, lhs->tag, dfs(lhs->conn.l, rhs->conn.l), dfs(lhs->conn.r, rhs->conn.r));
        case FORALL: case EXISTS: case UNIQUE: case FORALL2: case LAM:
          if (lhs->binder.arity != rhs->binder.arity || lhs->binder.sort != rhs->binder.sort) {
            return different();
          }
          return Expr::make(*pool, lhs->tag,
            lhs->bv, lhs->binder.arity, lhs->binder.sort,
            dfs(lhs->binder.r, rhs->binder.r));
      }
      throw NotImplemented();
    }

    tuple<Expr*, Subs, Subs> operator()(unsigned int offset, Allocator<Expr>* pool, const Expr* lhs, const Expr* rhs) {
      this->pool = pool;
      ls.offset = rs.offset = this->nextid = offset;
      ls.ts.clear(); rs.ts.clear();
      Expr* c = dfs(lhs, rhs);
      return { c, ls, rs };
    }
  };

  tuple<Expr*, Subs, Subs> antiunify(unsigned int offset, const Expr* l, const Expr* r, Allocator<Expr>& pool) {
    return Antiunifier()(offset, &pool, l, r);
  }

  // The Robinson's unification algorithm (could take exponential time for certain cases.)
  // See: https://en.wikipedia.org/wiki/Unification_(computer_science)#A_unification_algorithm
  optional<Subs> unify(unsigned int offset, vector<pair<const Expr*, const Expr*>> a, Allocator<Expr>& pool) {
    using enum Expr::Tag;

    Subs res{ offset, vector<const Expr*>() };
    auto putsubs = [&res, &pool, &a] (unsigned int id, const Expr* e, size_t i0) {
      // Make enough space
      while (id >= res.offset + res.ts.size()) {
        res.ts.push_back(nullptr);
      }
      // id < res.offset + res.ts.size()
      res.ts[id - res.offset] = e;
      // Update the rest of `a`
      auto f = [id, e, &pool] (unsigned int, Expr* x) {
        if (x->var.free && x->var.id == id) return e->clone(pool);
        return x;
      };
      for (size_t i = i0; i < a.size(); i++) {
        a[i].first = a[i].first->updateVars(0, pool, f);
        a[i].second = a[i].second->updateVars(0, pool, f);
      }
    };

    for (size_t i = 0; i < a.size(); i++) {
      const Expr* lhs = a[i].first, * rhs = a[i].second;

      if (lhs->tag == VAR && lhs->var.free && lhs->var.id >= offset) {
        if (*lhs == *rhs);
        else if (rhs->occurs(lhs->var.id)) return nullopt;
        else putsubs(lhs->var.id, rhs, i + 1);
        continue;

      } else if (rhs->tag == VAR && rhs->var.free && rhs->var.id >= offset) {
        if (*lhs == *rhs);
        else if (lhs->occurs(rhs->var.id)) return nullopt;
        else putsubs(rhs->var.id, lhs, i + 1);
        continue;

      } else {
        if (lhs->tag != rhs->tag) return nullopt;
        // lhs->tag == rhs->tag
        switch (lhs->tag) {
          case EMPTY:
            throw Unreachable();
          case VAR: {
            if (lhs->var.free != rhs->var.free || lhs->var.id != rhs->var.id) return nullopt;
            const Expr* plhs = lhs->var.c, * prhs = rhs->var.c;
            for (; plhs && prhs; plhs = plhs->s, prhs = prhs->s) {
              a.emplace_back(plhs, prhs);
            }
            if (plhs || prhs) throw Unreachable();
            break;
          }
          case TRUE: case FALSE:
            break;
          case NOT:
            a.emplace_back(lhs->conn.l, rhs->conn.l);
            break;
          case AND: case OR: case IMPLIES: case IFF:
            a.emplace_back(lhs->conn.l, rhs->conn.l);
            a.emplace_back(lhs->conn.r, rhs->conn.r);
            break;
          case FORALL: case EXISTS: case UNIQUE: case FORALL2: case LAM:
            if (lhs->binder.arity != rhs->binder.arity || lhs->binder.sort != rhs->binder.sort) {
              return nullopt;
            }
            a.emplace_back(lhs->binder.r, rhs->binder.r);
            break;
        }
        continue;
      }
    }

    return res;
  }

  /*
  // The Martelli-Montanari unification algorithm.
  // All free variables with `id >= offset` are considered as undetermined variables; others are just constants.
  // See: http://moscova.inria.fr/~levy/courses/X/IF/03/pi/levy2/martelli-montanari.pdf
  optional<Subs> mmunify(unsigned int offset, vector<pair<const Expr*, const Expr*>> a, Allocator<Expr>& pool) {
    using enum Expr::Tag;

    *
    * Side note: so what Tony Field described here is not the real Martelli-Montanari:
    * https://www.doc.ic.ac.uk/~ajf/haskelltests/typeinference/spec.pdf
    * This method could take exponential time on certain cases, as discussed in the Martelli-Montanari paper...
    * e.g. consider the following constructions:
    *
    * ```
    * left :: Int -> Type
    * left n
    *   | n == 0    = TFun (TFun (TVar s) (TVar s)) (TVar s)
    *   | otherwise = TFun (TFun (left (n - 1)) (TVar s)) (TVar s)
    *   where s = "v" ++ show n
    *
    * right :: Int -> Type
    * right n
    *   | n == 0    = TFun (TFun (TVar s) (TVar s)) (TVar s)
    *   | otherwise = TFun (TFun (TVar s) (right (n - 1))) (TVar s)
    *   where s = "v" ++ show n
    * ```
    *
    * Now run: `unify (left 15) (right 15)`. It may take half a minute to complete.
    * Changing 15 to 20 will cause stack overflow.
    * (There's another problem with the `applySub` function defined in the spec; it only works when
    *  the RHS of every substitution does not contain other variables, but is easy to fix.)
    *

    return res;
  }
  */

}
