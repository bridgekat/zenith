#include <algorithm>
#include <iostream>
#include "tableau.hpp"

#define SEMANTIC_BRANCHING


namespace Elab {

  using Procs::Subs;

  // Simple case: disjoint
  Subs simpleCompose(const Subs& a, const Subs& b) noexcept {
    Subs res(std::max(a.size(), b.size()), nullptr);
    for (size_t i = 0; i < res.size(); i++) {
      bool af = i < a.size() && a[i], bf = i < b.size() && b[i];
      if (af && bf) throw Unreachable();
      res[i] = af ? a[i] : bf ? b[i] : nullptr;
    }
    return res;
  }

  string typeToString(unsigned int t) noexcept {
    using enum Tableau::Type;
    switch (t) {
      case ι: return "ι";
      case α: return "α";
      case β: return "β";
      case γ: return "γ";
      case δ: return "δ";
      case γre: return "γre";
    }
    return "?";
  }

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
    ExprHash ehash;
    bool inserted, reAdd;

    WithCedent(Tableau* p, const Expr* e, bool* closed, bool reAdd = false):
        p(p), i(Tableau::classify(LR, e)), ehash(ExprHash(e)), inserted(false), reAdd(reAdd) {
      if (reAdd) i = Tableau::Type::γre; // TODO: make least priority
      inserted = p->hashset[LR].insert(ehash).second;
      if (inserted) {
        // Try hash set first
        if (p->hashset[RL].contains(ehash)) {
          *closed = true;
          p->closed++;
          std::cout << "Branch closed" << std::endl;
        } else {
          // Compare one by one, taking substitution into consideration
          // TODO: try optimise candidate selection...
          //unsigned int j = Tableau::classify(RL, e);
          //for (const Expr* q: p->cedents[j][RL])
          for (auto& [q, _]: p->hashset[RL])
            if (Procs::equalAfterSubs(e, q, p->subs)) {
              *closed = true;
              p->closed++;
              std::cout << "Branch closed" << std::endl;
              break;
            }
        }
      }
      if (inserted || reAdd) p->cedents[i][LR].push_back(e);
    }
    WithCedent(const WithCedent&) = delete;
    WithCedent& operator=(const WithCedent&) = delete;
    ~WithCedent() {
      if (inserted || reAdd) p->cedents[i][LR].pop_back();
      if (inserted) p->hashset[LR].erase(ehash);
    }
  };

  using WithAnte = WithCedent<Tableau::Position::L, Tableau::Position::R>;
  using WithSucc = WithCedent<Tableau::Position::R, Tableau::Position::L>;

  // Pre: all elements of `ante`, `succ`, `anteSet` and `succSet` are valid, well-formed formulas
  // All states will be unmodified/restored
  bool Tableau::dfs(size_t depth) {
    if (depth >= maxDepth) {
      maxDepthReached = maxDepth;
      return false;
    }
    maxDepthReached = std::max(maxDepthReached, depth);
    invocations++;

    // Tweak parameters here (3/3)
    constexpr static unsigned int order[] = { α, δ, γ, ι, β, γre };
    //constexpr static int Kι = 3; // One ι-expansion = how many β-expansions?
    //constexpr static int Kγ = 1; // One γ-expansion = how many β-expansions?

    for (unsigned int i: order) {
      using enum Expr::Tag;
      using enum Expr::VarTag;
      auto&   ante  = cedents[i][L], & succ  = cedents[i][R];
      size_t& antei = indices[i][L], & succi = indices[i][R];

      // Right logical rules (try breaking down one succedent)
      if (succi < succ.size()) {
        const Expr* e = succ[succi];
        WithValue iguard(&succi, succi + 1);

        const Expr* es = Procs::applySubs(e, subs, pool);
        std::cout << string(depth * 2, ' ') << "F (" << typeToString(i) << ") " << es->toString(ctx) << std::endl;

        switch (e->tag) {
          case VAR: {
            // iota
            // Try unify and close branch (no need to check for other closures...)
            // TODO: try optimise candidate selection...
            const Expr* es = Procs::applySubs(e, subs, pool);
            //unsigned int j = classify(L, es);
            //for (const Expr* q: cedents[j][L]) {
            for (auto& [q, _]: hashset[L]) {
              auto res = Procs::unify({{ es, Procs::applySubs(q, subs, pool) }}, pool);
              if (res.has_value()) {
                // TODO: is this complete?
                subs = simpleCompose(subs, res.value());
                if (!Procs::equalAfterSubs(e, q, subs)) throw Unreachable();
                closed++;
                std::cout << "Branch closed" << std::endl;
                return true;
              }
            }
            return dfs(depth);
          }
          case TRUE:
            std::cout << "Branch closed" << std::endl;
            return true;
          case FALSE:
            return dfs(depth);
          case NOT: {
            bool closed = false;
            WithAnte n(this, e->conn.l, &closed);
            return closed || dfs(depth);
          }
          case AND: {
            // beta
            {
              bool closed = false;
              WithSucc l(this, e->conn.l, &closed);
              if (!closed && !dfs(depth + 1)) return false;
            }
            branches++;
            {
              bool closed = false;
              WithSucc r(this, e->conn.r, &closed);
              #ifdef SEMANTIC_BRANCHING
              WithAnte l(this, e->conn.l, &closed);
              #endif
              if (!closed && !dfs(depth)) return false;
            }
            return true;
          }
          case OR: {
            // alpha
            bool closed = false;
            WithSucc l(this, e->conn.l, &closed);
            WithSucc r(this, e->conn.r, &closed);
            return closed || dfs(depth);
          }
          case IMPLIES: {
            // alpha
            bool closed = false;
            WithAnte l(this, e->conn.l, &closed);
            WithSucc r(this, e->conn.r, &closed);
            return closed || dfs(depth);
          }
          case IFF: {
            // beta
            Expr mp(IMPLIES, e->conn.l, e->conn.r);
            Expr mpr(IMPLIES, e->conn.r, e->conn.l);
            {
              bool closed = false;
              WithSucc l(this, &mp, &closed);
              if (!closed && !dfs(depth + 1)) return false;
            }
            branches++;
            {
              bool closed = false;
              WithSucc r(this, &mpr, &closed);
              #ifdef SEMANTIC_BRANCHING
              WithAnte l(this, &mp, &closed);
              #endif
              if (!closed && !dfs(depth)) return false;
            }
            return true;
          }
          case FORALL: {
            // delta
            bool closed = false;
            vector<Expr*> univ;
            for (size_t j = 0; j < numUniversal; j++) univ.push_back(Expr::make(pool, UNDETERMINED, j));
            size_t id = numSkolem + ctx.size();
            Expr newVar(FREE, id, univ);
            const Expr* body = e->binder.r->makeReplace(&newVar, pool);
            WithValue n(&numSkolem, numSkolem + 1);
            WithSucc l(this, body, &closed);
            WithSucc r(this, e, &closed);
            return closed || dfs(depth);
          }
          case EXISTS: {
            // gamma
            bool closed = false;
            size_t id = numUniversal;
            Expr newVar(UNDETERMINED, id);
            const Expr* body = e->binder.r->makeReplace(&newVar, pool);
            WithValue n(&numUniversal, numUniversal + 1);
            WithSucc l(this, body, &closed);
            WithSucc r(this, e, &closed, true); // Re-add
            return closed || dfs(i == γre ? depth + 1 : depth);
          }
          case UNIQUE: {
            // beta
            Expr exi(EXISTS, e->bv, e->binder.arity, e->binder.sort, e->binder.r);
            {
              bool closed = false;
              WithSucc l(this, &exi, &closed);
              if (!closed && !dfs(depth + 1)) return false;
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
              WithSucc r(this, &no2, &closed);
              #ifdef SEMANTIC_BRANCHING
              WithAnte l(this, &exi, &closed);
              #endif
              if (!closed && !dfs(depth)) return false;
            }
            return true;
          }
          case FORALL2: {
            // TODO: second-order delta rule
            return dfs(depth);
          }
          case EMPTY: case LAM:
            return dfs(depth);
        }
        throw NotImplemented();
      }

      // Left logical rules (try breaking down one antecedent)
      if (antei < ante.size()) {
        const Expr* e = ante[antei];
        WithValue iguard(&antei, antei + 1);

        const Expr* es = Procs::applySubs(e, subs, pool);
        std::cout << string(depth * 2, ' ') << "T (" << typeToString(i) << ") " << es->toString(ctx) << std::endl;

        switch (e->tag) {
          case VAR: {
            // iota
            // Try unify and close branch (no need to check for other closures...)
            // TODO: try optimise candidate selection...
            const Expr* es = Procs::applySubs(e, subs, pool);
            //unsigned int j = classify(R, es);
            //for (const Expr* q: cedents[j][R]) {
            for (auto& [q, _]: hashset[R]) {
              auto res = Procs::unify({{ es, Procs::applySubs(q, subs, pool) }}, pool);
              if (res.has_value()) {
                // TODO: is this complete?
                subs = simpleCompose(subs, res.value());
                if (!Procs::equalAfterSubs(e, q, subs)) throw Unreachable();
                closed++;
                std::cout << "Branch closed" << std::endl;
                return true;
              }
            }
            return dfs(depth);
          }
          case TRUE:
            return dfs(depth);
          case FALSE:
            std::cout << "Branch closed" << std::endl;
            return true;
          case NOT: {
            bool closed = false;
            WithSucc n(this, e->conn.l, &closed);
            return closed || dfs(depth);
          }
          case AND: {
            // alpha
            bool closed = false;
            WithAnte l(this, e->conn.l, &closed);
            WithAnte r(this, e->conn.r, &closed);
            return closed || dfs(depth);
          }
          case OR: {
            // beta
            {
              bool closed = false;
              WithAnte l(this, e->conn.l, &closed);
              if (!closed && !dfs(depth + 1)) return false;
            }
            branches++;
            {
              bool closed = false;
              WithAnte r(this, e->conn.r, &closed);
              #ifdef SEMANTIC_BRANCHING
              WithSucc l(this, e->conn.l, &closed);
              #endif
              if (!closed && !dfs(depth)) return false;
            }
            return true;
          }
          case IMPLIES: {
            // beta
            {
              bool closed = false;
              WithSucc n(this, e->conn.l, &closed);
              if (!closed && !dfs(depth + 1)) return false;
            }
            branches++;
            {
              bool closed = false;
              WithAnte r(this, e->conn.r, &closed);
              #ifdef SEMANTIC_BRANCHING
              WithAnte l(this, e->conn.l, &closed);
              #endif
              if (!closed && !dfs(depth)) return false;
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
            return closed || dfs(depth);
          }
          case FORALL: {
            // gamma
            bool closed = false;
            size_t id = numUniversal;
            Expr newVar(UNDETERMINED, id);
            const Expr* body = e->binder.r->makeReplace(&newVar, pool);
            WithValue n(&numUniversal, numUniversal + 1);
            WithAnte l(this, body, &closed);
            WithAnte r(this, e, &closed, true); // Re-add
            return closed || dfs(i == γre ? depth + 1 : depth);
          }
          case EXISTS: {
            // delta
            bool closed = false;
            vector<Expr*> univ;
            for (size_t j = 0; j < numUniversal; j++) univ.push_back(Expr::make(pool, UNDETERMINED, j));
            size_t id = numSkolem + ctx.size();
            Expr newVar(FREE, id, univ);
            const Expr* body = e->binder.r->makeReplace(&newVar, pool);
            WithValue n(&numSkolem, numSkolem + 1);
            WithAnte l(this, body, &closed);
            WithAnte r(this, e, &closed);
            return closed || dfs(depth);
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
            return closed || dfs(depth);
          }
          case FORALL2: {
            // "φ" rule is not supported yet...
            return dfs(depth);
          }
          case EMPTY: case LAM:
            return dfs(depth);
        }
        throw NotImplemented();
      }
    }

    // We have used up everything and the branch is still not closed
    return false;
  }

  bool Tableau::search(size_t maxDepth) {
    for (unsigned int i = 0; i < N; i++) {
      indices[i][L] = 0;
      indices[i][R] = 0;
    }
    numUniversal = numSkolem = 0;
    subs.clear();
    maxDepthReached = 0;
    invocations = 0;
    branches = 1;
    closed = 0;
    this->maxDepth = maxDepth;
    return dfs(0);
  }

  string Tableau::printState() {
    string res;
    res += "+------------------------------------\n";
    for (unsigned int i = 0; i < N; i++) for (const Expr* e: cedents[i][L])
      res += "| " + e->toString(ctx) + "\n";
    for (unsigned int i = 0; i < N; i++) for (const Expr* e: cedents[i][R])
      res += "| ⊢ " + e->toString(ctx) + "\n";
    res += "+------------------------------------\n";
    return res;
  }

  string Tableau::printStateDebug() {
    string res;
    res += "+------------------------------------\n";
    for (unsigned int i = 0; i < N; i++) {
      res += "| (" + typeToString(i) + ") " + std::to_string(indices[i][L]) + "\n";
      for (const Expr* e: cedents[i][L])
        res += "| " + e->toString(ctx) + "\n";
    }
    for (unsigned int i = 0; i < N; i++) {
      res += "| (" + typeToString(i) + ") " + std::to_string(indices[i][R]) + "\n";
      for (const Expr* e: cedents[i][R])
        res += "| ⊢ " + e->toString(ctx) + "\n";
    }
    res += "+------------------------------------\n";
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
