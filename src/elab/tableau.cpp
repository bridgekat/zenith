#include <algorithm>
#include "tableau.hpp"

namespace Elab {

  // Tweak parameters here (2/3)
  Tableau::Type Tableau::classify(Position antesucc, const Expr* e) noexcept {
    using enum Expr::Tag;
    switch (antesucc) {
      case L:
        switch (e->tag) {
          case VAR:     return ι;
          case TRUE:    return α;
          case FALSE:   return α;
          case NOT:     return α;
          case AND:     return α;
          case OR:      return β;
          case IMPLIES: return β;
          case IFF:     return α;
          case FORALL:  return γ;
          case EXISTS:  return δ;
          case UNIQUE:  return α;
          case FORALL2: return α; // Change to return φ; when ready
          case EMPTY: case LAM: return α;
        }
        break;
      case R:
        switch (e->tag) {
          case VAR:     return ι;
          case TRUE:    return α;
          case FALSE:   return α;
          case NOT:     return α;
          case AND:     return β;
          case OR:      return α;
          case IMPLIES: return α;
          case IFF:     return β;
          case FORALL:  return δ;
          case EXISTS:  return γ;
          case UNIQUE:  return β;
          case FORALL2: return δ;
          case EMPTY: case LAM: return α;
        }
        break;
    }
    throw Core::NotImplemented();
  }

  // Scope guard for "change value, recurse, and change back"
  template <typename T>
  class WithValue {
  public:
    T* p, prev;
    WithValue(T* p, const T& value): p(p), prev(*p) { *p = value; }
    WithValue(const WithValue&) = delete;
    WithValue& operator=(const WithValue&) = delete;
    ~WithValue() { *p = prev; }
  };

  // Scope guard for "insert antecedents/succedents, check if closed, recurse, and remove them"
  template <Tableau::Position LR, Tableau::Position RL>
  class WithCedent {
  public:
    Tableau* const p;
    Tableau::Type i;
    pair<unordered_set<ExprHash, ExprHash::GetHash>::iterator, bool> it;

    WithCedent(Tableau* p, const Expr* e, bool* closed): p(p), i(Tableau::classify(LR, e)), it() {
      ExprHash ehash = ExprHash(e);
      it = p->hashset[LR].insert(ehash);
      if (it.second) {
        p->cedents[i][LR].push_back(e);
        if (p->hashset[RL].contains(ehash)) {
          *closed = true;
          p->closed++;
        }
      }
    }
    WithCedent(const WithCedent&) = delete;
    WithCedent& operator=(const WithCedent&) = delete;
    ~WithCedent() {
      if (it.second) {
        p->cedents[i][LR].pop_back();
        p->hashset[LR].erase(it.first);
      }
    }
  };

  using WithAnte = WithCedent<Tableau::Position::L, Tableau::Position::R>;
  using WithSucc = WithCedent<Tableau::Position::R, Tableau::Position::L>;

  // Pre: all elements of `ante`, `succ`, `anteSet` and `succSet` are valid, well-formed formulas
  // All states will be unmodified/restored
  bool Tableau::dfs(int maxDepth) {
    if (maxDepth <= 0) {
      maxDepthReached = 0;
      return false;
    }
    maxDepthReached = std::min(maxDepthReached, maxDepth);
    invocations++;

    // Tweak parameters here (3/3)
    constexpr static unsigned int order[] = { α, δ, γ, ι, β };
    //const static unsigned int order[] = { α, δ, γ, ι, β };
    constexpr static int Kι = 3; // One ι-expansion = how many β-expansions?
    constexpr static int Kγ = 1; // One γ-expansion = how many β-expansions?

    for (unsigned int i: order) {
      using enum Expr::Tag;
      using enum Expr::VarTag;
      auto&   ante  = cedents[i][L], & succ  = cedents[i][R];
      size_t& antei = indices[i][L], & succi = indices[i][R];

      // Right logical rules (try breaking down one succedent)
      if (succi < succ.size()) {
        const Expr* e = succ[succi];
        WithValue iguard(&succi, succi + 1);

        switch (e->tag) {
          case VAR: {
            // TODO: try unify and close branch?
            return dfs(maxDepth - Kι);
          }
          case TRUE:
            return true;
          case FALSE:
            return dfs(maxDepth);
          case NOT: {
            bool closed = false;
            WithAnte n(this, e->conn.l, &closed);
            return closed || dfs(maxDepth);
          }
          case AND: {
            // beta
            {
              bool closed = false;
              WithSucc l(this, e->conn.l, &closed);
              if (!closed && !dfs(maxDepth - 1)) return false;
            }
            branches++;
            {
              bool closed = false;
              WithAnte l(this, e->conn.l, &closed); // Optimization
              WithSucc r(this, e->conn.r, &closed);
              if (!closed && !dfs(maxDepth - 1)) return false;
            }
            return true;
          }
          case OR: {
            // alpha
            bool closed = false;
            WithSucc l(this, e->conn.l, &closed);
            WithSucc r(this, e->conn.r, &closed);
            return closed || dfs(maxDepth);
          }
          case IMPLIES: {
            // alpha
            bool closed = false;
            WithAnte l(this, e->conn.l, &closed);
            WithSucc r(this, e->conn.r, &closed);
            return closed || dfs(maxDepth);
          }
          case IFF: {
            // beta
            Expr mp(IMPLIES, e->conn.l, e->conn.r);
            Expr mpr(IMPLIES, e->conn.r, e->conn.l);
            {
              bool closed = false;
              WithSucc l(this, &mp, &closed);
              if (!closed && !dfs(maxDepth - 1)) return false;
            }
            branches++;
            {
              bool closed = false;
              WithAnte l(this, &mp, &closed); // Optimization
              WithSucc r(this, &mpr, &closed);
              if (!closed && !dfs(maxDepth - 1)) return false;
            }
            return true;
          }
          case FORALL: {
            bool closed = false;
            size_t id = numSkolem + ctx.size();
            Expr newVar(FREE, id);
            const Expr* body = e->binder.r->makeReplace(&newVar, pool);
            WithValue n(&numSkolem, numSkolem + 1);
            WithSucc l(this, body, &closed);
            WithSucc r(this, e, &closed);
            return closed || dfs(maxDepth);
          }
          case EXISTS: {
            // gamma
            bool closed = false;
            size_t id = numUniversal;
            Expr newVar(UNDETERMINED, id);
            const Expr* body = e->binder.r->makeReplace(&newVar, pool);
            WithValue n(&numUniversal, numUniversal + 1);
            WithSucc l(this, body, &closed);
            WithSucc r(this, e, &closed);
            return closed || dfs(maxDepth - Kγ);
          }
          case UNIQUE: {
            // beta
            Expr exi(EXISTS, e->bv, e->binder.arity, e->binder.sort, e->binder.r);
            {
              bool closed = false;
              WithSucc l(this, &exi, &closed);
              if (!closed && !dfs(maxDepth - 1)) return false;
            }
            Expr x(BOUND, 1), x_(BOUND, 0);
            Expr eq(FREE, ctx.eq, { &x, &x_ });
            Expr d(IMPLIES, e->binder.r, &eq);
            Expr c(FORALL, e->bv + "'", e->binder.arity, e->binder.sort, &d);
            Expr b(IMPLIES, e->binder.r, &c);
            Expr a(FORALL, e->bv, e->binder.arity, e->binder.sort, &b);
            Expr no2 = a;
            branches++;
            {
              bool closed = false;
              WithAnte l(this, &exi, &closed); // Optimization
              WithSucc r(this, &no2, &closed);
              if (!closed && !dfs(maxDepth - 1)) return false;
            }
            return true;
          }
          case FORALL2: {
            // TODO: second-order delta rule
            return dfs(maxDepth);
          }
          case EMPTY: case LAM:
            return dfs(maxDepth);
        }
        throw NotImplemented();
      }

      // Left logical rules (try breaking down one antecedent)
      if (antei < ante.size()) {
        const Expr* e = ante[antei];
        WithValue iguard(&antei, antei + 1);

        switch (e->tag) {
          case VAR: {
            // TODO: try unify and close branch?
            return dfs(maxDepth - Kι);
          }
          case TRUE:
            return dfs(maxDepth);
          case FALSE:
            return true;
          case NOT: {
            bool closed = false;
            WithSucc n(this, e->conn.l, &closed);
            return closed || dfs(maxDepth);
          }
          case AND: {
            // alpha
            bool closed = false;
            WithAnte l(this, e->conn.l, &closed);
            WithAnte r(this, e->conn.r, &closed);
            return closed || dfs(maxDepth);
          }
          case OR: {
            // beta
            {
              bool closed = false;
              WithAnte l(this, e->conn.l, &closed);
              if (!closed && !dfs(maxDepth - 1)) return false;
            }
            branches++;
            {
              bool closed = false;
              WithSucc l(this, e->conn.l, &closed); // Optimization
              WithAnte r(this, e->conn.r, &closed);
              if (!closed && !dfs(maxDepth - 1)) return false;
            }
            return true;
          }
          case IMPLIES: {
            // beta
            {
              bool closed = false;
              WithSucc n(this, e->conn.l, &closed);
              if (!closed && !dfs(maxDepth - 1)) return false;
            }
            branches++;
            {
              bool closed = false;
              WithAnte l(this, e->conn.l, &closed); // Optimization
              WithAnte r(this, e->conn.r, &closed);
              if (!closed && !dfs(maxDepth - 1)) return false;
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
            return closed || dfs(maxDepth);
          }
          case FORALL: {
            // gamma
            bool closed = false;
            size_t id = numUniversal;
            Expr newVar(UNDETERMINED, id);
            const Expr* body = e->binder.r->makeReplace(&newVar, pool);
            WithValue n(&numUniversal, numUniversal + 1);
            WithAnte l(this, body, &closed);
            WithAnte r(this, e, &closed);
            return closed || dfs(maxDepth - Kγ);
          }
          case EXISTS: {
            // delta
            bool closed = false;
            size_t id = numSkolem + ctx.size();
            Expr newVar(FREE, id);
            const Expr* body = e->binder.r->makeReplace(&newVar, pool);
            WithValue n(&numSkolem, numSkolem + 1);
            WithAnte l(this, body, &closed);
            WithAnte r(this, e, &closed);
            return closed || dfs(maxDepth);
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
            WithAnte r(this, &no2, &closed);
            return closed || dfs(maxDepth);
          }
          case FORALL2: {
            // "φ" rule is not supported yet...
            return dfs(maxDepth);
          }
          case EMPTY: case LAM:
            return dfs(maxDepth);
        }
        throw NotImplemented();
      }
    }

    // We have used up everything and the branch is still not closed
    return false;
  }

  bool Tableau::search(int maxDepth) {
    numUniversal = numSkolem = 0;
    subs.clear();
    maxDepthReached = maxDepth;
    invocations = 0;
    branches = 1;
    closed = 0;
    bool res = dfs(maxDepth);
    maxDepthReached = maxDepth - maxDepthReached;
    return res;
  }

  string Tableau::printStats() {
    string res;
    res += "+------------------------------------\n";
    res += "| Number of DFS invocations: " + std::to_string(invocations) + "\n";
    res += "| Maximum beta-depth: " + std::to_string(maxDepthReached) + "\n";
    res += "| Total number of opened branches: " + std::to_string(branches) + "\n";
    res += "| Total number of closed branches: " + std::to_string(closed) + "\n";
    res += "+------------------------------------\n";
    return res;
  }

}
