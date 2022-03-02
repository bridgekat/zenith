#include "tableau.hpp"

namespace Elab {

  // Scope guard for "insert antecedents/succedents, check if closed, recurse, and remove them"
  template <unsigned int I, unsigned int J>
  class With {
  public:
    Tableau* const p;
    pair<unordered_set<ExprHash, ExprHash::GetHash>::iterator, bool> it;
    With(Tableau* p, const Expr* e, bool* closed): p(p), it() {
      ExprHash ehash = ExprHash(e);
      it = p->hashset[I].insert(ehash);
      if (it.second) {
        p->cedents[I].push_back(e);
        if (p->hashset[J].contains(ehash)) *closed = true;
      }
    }
    With(const With&) = delete;
    With& operator=(const With&) = delete;
    ~With() {
      if (it.second) {
        p->cedents[I].pop_back();
        p->hashset[I].erase(it.first);
      }
    }
  };
  using WithAnte = With<0, 1>;
  using WithSucc = With<1, 0>;

  // TODO: alpha > delta > gamma > beta?
  bool Tableau::dfs(size_t antei, size_t succi) {
    using enum Expr::Tag;
    auto ante = cedents[0], succ = cedents[1];

    // Left logical rules (try breaking down one antecedent)
    if (antei < ante.size()) {
      const Expr* e = ante[antei];
      antei++;
      switch (e->tag) {
        case VAR: {
          // TODO: try unify and close branch?
          return dfs(antei, succi);
        }
        case TRUE:
          return dfs(antei, succi);
        case FALSE:
          return true;
        case NOT: {
          bool closed = false;
          WithSucc n(this, e->conn.l, &closed);
          return closed || dfs(antei, succi);
        }
        case AND: {
          // alpha
          bool closed = false;
          WithAnte l(this, e->conn.l, &closed);
          WithAnte r(this, e->conn.r, &closed);
          return closed || dfs(antei, succi);
        }
        case OR: {
          // beta
          {
            bool closed = false;
            WithAnte l(this, e->conn.l, &closed);
            if (!closed && !dfs(antei, succi)) return false;
          }
          {
            bool closed = false;
            WithSucc l(this, e->conn.l, &closed); // Optimization
            WithAnte r(this, e->conn.r, &closed);
            if (!closed && !dfs(antei, succi)) return false;
          }
          return true;
        }
        case IMPLIES: {
          // beta
          {
            bool closed = false;
            WithSucc n(this, e->conn.l, &closed);
            if (!closed && !dfs(antei, succi)) return false;
          }
          {
            bool closed = false;
            WithAnte l(this, e->conn.l, &closed); // Optimization
            WithAnte r(this, e->conn.r, &closed);
            if (!closed && !dfs(antei, succi)) return false;
          }
          return true;
        }
        case IFF: {
          // alpha
          Expr mp(IMPLIES, e->conn.l, e->conn.r);
          Expr mpr(IMPLIES, e->conn.r, e->conn.l);
          bool closed = false;
          WithAnte l(this, &mp, &closed);
          WithAnte r(this, &mpr, &closed);
          return closed || dfs(antei, succi);
        }
        case FORALL: {
          // TODO: gamma
          return dfs(antei, succi);
        }
        case EXISTS: {
          // TODO: delta
          return dfs(antei, succi);
        }
        case UNIQUE: {
          // alpha
          Expr exi(EXISTS, e->bv, e->binder.arity, e->binder.sort, e->binder.r);
          Expr x(BOUND, 1), x_(BOUND, 0);
          Expr eq(FREE, ctx.eq, { &x, &x_ });
          Expr d(IMPLIES, e->binder.r, &eq);
          Expr c(FORALL, e->bv + "'", e->binder.arity, e->binder.sort, &d);
          Expr b(IMPLIES, e->binder.r, &c);
          Expr a(FORALL, e->bv, e->binder.arity, e->binder.sort, &b);
          Expr no2 = a;
          bool closed = false;
          WithAnte l(this, &exi, &closed);
          WithAnte l(this, &no2, &closed);
          return closed || dfs(antei, succi);
        }
        case FORALL2: {
          // Second-order formulas are not supported yet...
          return dfs(antei, succi);
        }
        case EMPTY: case LAM:
          return dfs(antei, succi);
      }
      throw NotImplemented();
    }

    // Right logical rules (try breaking down one succedent)
    if (succi < succ.size()) {
      const Expr* e = succ[succi];
      succi++;
      switch (e->tag) {
        case VAR: {
          // TODO: try unify and close branch?
          return dfs(antei, succi);
        }
        case TRUE:
          return true;
        case FALSE:
          return dfs(antei, succi);
        case NOT: {
          bool closed = false;
          WithAnte n(this, e->conn.l, &closed);
          return closed || dfs(antei, succi);
        }
        case AND: {
          // beta
          {
            bool closed = false;
            WithSucc l(this, e->conn.l, &closed);
            if (!closed && !dfs(antei, succi)) return false;
          }
          {
            bool closed = false;
            WithAnte l(this, e->conn.l, &closed); // Optimization
            WithSucc r(this, e->conn.r, &closed);
            if (!closed && !dfs(antei, succi)) return false;
          }
          return true;
        }
        case OR: {
          // alpha
          bool closed = false;
          WithSucc l(this, e->conn.l, &closed);
          WithSucc r(this, e->conn.r, &closed);
          return closed || dfs(antei, succi);
        }
        case IMPLIES: {
          // alpha
          bool closed = false;
          WithAnte l(this, e->conn.l, &closed);
          WithSucc r(this, e->conn.r, &closed);
          return closed || dfs(antei, succi);
        }
        case IFF: {
          // beta
          Expr mp(IMPLIES, e->conn.l, e->conn.r);
          Expr mpr(IMPLIES, e->conn.r, e->conn.l);
          {
            bool closed = false;
            WithSucc l(this, &mp, &closed);
            if (!closed && !dfs(antei, succi)) return false;
          }
          {
            bool closed = false;
            WithAnte l(this, &mp, &closed); // Optimization
            WithSucc r(this, &mpr, &closed);
            if (!closed && !dfs(antei, succi)) return false;
          }
          return true;
        }
        case FORALL: {
          // TODO: delta
          return dfs(antei, succi);
        }
        case EXISTS: {
          // TODO: gamma
          return dfs(antei, succi);
        }
        case UNIQUE: {
          // beta
          Expr exi(EXISTS, e->bv, e->binder.arity, e->binder.sort, e->binder.r);
          {
            bool closed = false;
            WithSucc l(this, &exi, &closed);
            if (!closed && !dfs(antei, succi)) return false;
          }
          Expr x(BOUND, 1), x_(BOUND, 0);
          Expr eq(FREE, ctx.eq, { &x, &x_ });
          Expr d(IMPLIES, e->binder.r, &eq);
          Expr c(FORALL, e->bv + "'", e->binder.arity, e->binder.sort, &d);
          Expr b(IMPLIES, e->binder.r, &c);
          Expr a(FORALL, e->bv, e->binder.arity, e->binder.sort, &b);
          Expr no2 = a;
          {
            bool closed = false;
            WithAnte l(this, &exi, &closed); // Optimization
            WithSucc r(this, &no2, &closed);
            if (!closed && !dfs(antei, succi)) return false;
          }
          return true;
        }
        case FORALL2: {
          // Second-order formulas are not supported yet...
          return dfs(antei, succi);
        }
        case EMPTY: case LAM:
          return dfs(antei, succi);
      }
      throw NotImplemented();
    }

    // We have used up everything and the branch is still not closed
    return false;
  }

}
