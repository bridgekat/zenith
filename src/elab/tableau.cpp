#include <algorithm>
#include <iostream>
#include "tableau.hpp"

#define SEMANTIC_BRANCHING
// #define PRINT_TRACE
// #define PRINT_CLOSURES


namespace Elab {

  using Procs::Subs;

  // Simple case: disjoint
  /*
  Subs simpleCompose(const Subs& a, const Subs& b) noexcept {
    Subs res(std::max(a.size(), b.size()), nullptr);
    for (size_t i = 0; i < res.size(); i++) {
      bool af = i < a.size() && a[i], bf = i < b.size() && b[i];
      if (af && bf) throw Unreachable();
      res[i] = af ? a[i] : bf ? b[i] : nullptr;
    }
    return res;
  }
  */

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

  // Apply `subs` to all of `cont`
  void Tableau::applySubs(const Subs& subs) {
    for (auto& branch: cont) {
      branch.hashset[L].clear();
      branch.hashset[R].clear();
      for (unsigned int i = 0; i < N; i++) {
        for (auto& e: branch.cedents[i][L]) {
          e = Procs::applySubs(e, subs, pools.back());
          branch.hashset[L].insert(ExprHash(e));
        }
        for (auto& e: branch.cedents[i][R]) {
          e = Procs::applySubs(e, subs, pools.back());
          branch.hashset[R].insert(ExprHash(e));
        }
      }
    }
  }

  // Check if `subs` does not contain variables with ID less than `offset`
  bool subsStartsFrom(const Subs& subs, size_t offset) {
    for (size_t i = 0; i < subs.size() && i < offset; i++) if (subs[i]) return false;
    return true;
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
      inserted = p->branch.hashset[LR].insert(ehash).second;
      if (inserted) {
        if (p->branch.hashset[RL].contains(ehash)) {
          *closed = true;
#ifdef PRINT_CLOSURES
          std::cout << "+------------------------------------" << std::endl;
          std::cout << "| Branch closed with:" << std::endl;
          std::cout << "| " << e->toString(p->ctx) << std::endl;
          std::cout << "+------------------------------------" << std::endl;
#endif
        }
      }
      if (inserted || reAdd) p->branch.cedents[i][LR].push_back(e);
    }
    WithCedent(const WithCedent&) = delete;
    WithCedent& operator=(const WithCedent&) = delete;
    ~WithCedent() {
      if (inserted || reAdd) p->branch.cedents[i][LR].pop_back();
      if (inserted) p->branch.hashset[LR].erase(ehash);
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
    constexpr static unsigned int order[] = { ι, α, δ, γ, β, γre };
    constexpr static int Kγre = 4; // One reentrant γ-expansion = how many β-expansions?

    auto closing = [this] (size_t newDepth) {
      if (cont.empty()) return true;
      WithValue stateguard(&branch, cont.back());
      cont.pop_back();
      bool res = dfs(newDepth);
      cont.push_back(branch);
      return res;
    };

    #define pool pools.back()
    for (unsigned int i: order) {
      using enum Expr::Tag;
      using enum Expr::VarTag;
      auto&   ante  = branch.cedents[i][L], & succ  = branch.cedents[i][R];
      size_t& antei = branch.indices[i][L], & succi = branch.indices[i][R];

      // Right logical rules (try breaking down one succedent)
      if (succi < succ.size()) {
        const Expr* e = succ[succi];
        WithValue iguard(&succi, succi + 1);

#ifdef PRINT_TRACE
        std::cout << string(cont.size() * 2, ' ') << "R (" << typeToString(i) << ") " << e->toString(ctx) << std::endl;
#endif

        switch (e->tag) {
          case VAR: {
            // iota
            // Try unify and close branch (no need to check for other closures...)
            // TODO: try optimise candidate selection...
            vector<Subs> unifiers;
            for (auto& [q, _]: branch.hashset[L]) {
              auto unifier = Procs::unify({{ e, q }}, pool);
              if (unifier.has_value()) {
                if (!Procs::equalAfterSubs(e, q, unifier.value())) throw Unreachable();
                // Optimization: if there's a unifier that doesn't affect other branches, we use that one and discard the rest.
                /*
                if (subsStartsFrom(unifier.value(), branch.numUniversalAbove)) {
                  unifiers.clear();
                  unifiers.push_back(unifier.value());
                  break;
                }
                */
                unifiers.push_back(unifier.value());
#ifdef PRINT_CLOSURES
                std::cout << "+------------------------------------" << std::endl;
                std::cout << "| Branch can be closed with:" << std::endl;
                std::cout << "| " << Procs::applySubs(e, unifier.value(), pool)->toString(ctx) << std::endl;
                std::cout << "+------------------------------------" << std::endl;
#endif
              }
            }
            if (!unifiers.empty()) {
              size_t id = backtrackPoints++;
#ifdef PRINT_TRACE
              std::cout << "** Creating backtracking choice point #" << id << std::endl;
#endif
              vector<Branch> backup = cont;
              for (const Subs& unifier: unifiers) {
#ifdef PRINT_TRACE
                std::cout << "************" << std::endl;
                std::cout << Procs::showSubs(unifier, ctx);
                std::cout << "************" << std::endl;
#endif
                pools.emplace_back();
                applySubs(unifier);
                bool res = closing(depth);
#ifdef PRINT_TRACE
                std::cout << "** Restoring to backtracking choice point #" << id << std::endl;
#endif
                cont = backup;
                pools.pop_back();
                if (res) return true;
              }
            }
            return dfs(depth);
          }
          case TRUE:
#ifdef PRINT_CLOSURES
            std::cout << "Branch closed with true at succedent" << std::endl;
#endif
            return closing(depth);
          case FALSE:
            return dfs(depth);
          case NOT: {
            bool closed = false;
            WithAnte n(this, e->conn.l, &closed);
            return closed? closing(depth) : dfs(depth);
          }
          case AND: {
            // beta
            branches++;
            WithValue nguard(&branch.numUniversalAbove, numUniversal);
            {
              bool closed = false;
              WithSucc r(this, e->conn.r, &closed);
#ifdef SEMANTIC_BRANCHING
              WithAnte l(this, e->conn.l, &closed);
#endif
              if (!closed) cont.push_back(branch);
            }
            bool closed = false;
            WithSucc l(this, e->conn.l, &closed);
            return closed? closing(depth) : dfs(depth + 1);
          }
          case OR: {
            // alpha
            bool closed = false;
            WithSucc l(this, e->conn.l, &closed);
            WithSucc r(this, e->conn.r, &closed);
            return closed? closing(depth) : dfs(depth);
          }
          case IMPLIES: {
            // alpha
            bool closed = false;
            WithAnte l(this, e->conn.l, &closed);
            WithSucc r(this, e->conn.r, &closed);
            return closed? closing(depth) : dfs(depth);
          }
          case IFF: {
            // beta
            branches++;
            WithValue nguard(&branch.numUniversalAbove, numUniversal);
            const Expr* mp = Expr::make(pool, IMPLIES, e->conn.l, e->conn.r);
            const Expr* mpr = Expr::make(pool, IMPLIES, e->conn.r, e->conn.l);
            {
              bool closed = false;
              WithSucc r(this, mpr, &closed);
#ifdef SEMANTIC_BRANCHING
              WithAnte l(this, mp, &closed);
#endif
              if (!closed) cont.push_back(branch);
            }
            bool closed = false;
            WithSucc l(this, mp, &closed);
            return closed? closing(depth) : dfs(depth + 1);
          }
          case FORALL: {
            // delta
            bool closed = false;
            vector<Expr*> univ;
            for (size_t j = 0; j < numUniversal; j++) univ.push_back(Expr::make(pool, UNDETERMINED, j));
            size_t id = numSkolem + ctx.size();
            Expr newVar(FREE, id, univ); // Disposable (will be copied to `pool` on the next line)
            const Expr* body = e->binder.r->makeReplace(&newVar, pool);
            WithValue n(&numSkolem, numSkolem + 1);
            WithSucc l(this, body, &closed);
            WithSucc r(this, e, &closed);
            return closed? closing(depth) : dfs(depth);
          }
          case EXISTS: {
            // gamma
            bool closed = false;
            size_t id = numUniversal;
            Expr newVar(UNDETERMINED, id); // Disposable (will be copied to `pool` on the next line)
            const Expr* body = e->binder.r->makeReplace(&newVar, pool);
            WithValue n(&numUniversal, numUniversal + 1);
            WithSucc l(this, body, &closed);
            WithSucc r(this, e, &closed, true); // Re-add
            return closed? closing(depth) : dfs(i == γre ? depth + Kγre : depth);
          }
          case UNIQUE: {
            // beta
            branches++;
            WithValue nguard(&branch.numUniversalAbove, numUniversal);
            const Expr* exi = Expr::make(pool, EXISTS, e->bv, e->binder.arity, e->binder.sort, e->binder.r);
            const Expr* no2 =
              Expr::make(pool, FORALL, e->bv, e->binder.arity, e->binder.sort,
              Expr::make(pool, IMPLIES, e->binder.r,
              Expr::make(pool, FORALL, e->bv + "'", e->binder.arity, e->binder.sort,
              Expr::make(pool, IMPLIES, e->binder.r,
              Expr::make(pool, FREE, ctx.eq, vector<Expr*>{ Expr::make(pool, BOUND, 1), Expr::make(pool, BOUND, 0) })))));
            {
              bool closed = false;
              WithSucc r(this, no2, &closed);
#ifdef SEMANTIC_BRANCHING
              WithAnte l(this, exi, &closed);
#endif
              if (!closed) cont.push_back(branch);
            }
            bool closed = false;
            WithSucc l(this, exi, &closed);
            return closed? closing(depth) : dfs(depth + 1);
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

#ifdef PRINT_TRACE
        std::cout << string(cont.size() * 2, ' ') << "L (" << typeToString(i) << ") " << e->toString(ctx) << std::endl;
#endif

        switch (e->tag) {
          case VAR: {
            // iota
            // Try unify and close branch (no need to check for other closures...)
            // TODO: try optimise candidate selection...
            vector<Subs> unifiers;
            for (auto& [q, _]: branch.hashset[R]) {
              auto unifier = Procs::unify({{ e, q }}, pool);
              if (unifier.has_value()) {
                if (!Procs::equalAfterSubs(e, q, unifier.value())) throw Unreachable();
                // Optimization: if there's a unifier that doesn't affect other branches, we use that one and discard the rest.
                /*
                if (subsStartsFrom(unifier.value(), branch.numUniversalAbove)) {
                  unifiers.clear();
                  unifiers.push_back(unifier.value());
                  break;
                }
                */
                unifiers.push_back(unifier.value());
#ifdef PRINT_CLOSURES
                std::cout << "+------------------------------------" << std::endl;
                std::cout << "| Branch can be closed with:" << std::endl;
                std::cout << "| " << Procs::applySubs(e, unifier.value(), pool)->toString(ctx) << std::endl;
                std::cout << "+------------------------------------" << std::endl;
#endif
              }
            }
            if (!unifiers.empty()) {
              size_t id = backtrackPoints++;
#ifdef PRINT_TRACE
              std::cout << "** Creating backtracking choice point #" << id << std::endl;
#endif
              vector<Branch> backup = cont;
              for (const Subs& unifier: unifiers) {
#ifdef PRINT_TRACE
                std::cout << "************" << std::endl;
                std::cout << Procs::showSubs(unifier, ctx);
                std::cout << "************" << std::endl;
#endif
                pools.emplace_back();
                applySubs(unifier);
                bool res = closing(depth);
#ifdef PRINT_TRACE
                std::cout << "** Restoring to backtracking choice point #" << id << std::endl;
#endif
                cont = backup;
                pools.pop_back();
                if (res) return true;
              }
            }
            return dfs(depth);
          }
          case TRUE:
            return dfs(depth);
          case FALSE:
#ifdef PRINT_CLOSURES
            std::cout << "Branch closed with false at antecedent" << std::endl;
#endif
            return closing(depth);
          case NOT: {
            bool closed = false;
            WithSucc n(this, e->conn.l, &closed);
            return closed? closing(depth) : dfs(depth);
          }
          case AND: {
            // alpha
            bool closed = false;
            WithAnte l(this, e->conn.l, &closed);
            WithAnte r(this, e->conn.r, &closed);
            return closed? closing(depth) : dfs(depth);
          }
          case OR: {
            // beta
            branches++;
            WithValue nguard(&branch.numUniversalAbove, numUniversal);
            {
              bool closed = false;
              WithAnte r(this, e->conn.r, &closed);
#ifdef SEMANTIC_BRANCHING
              WithSucc l(this, e->conn.l, &closed);
#endif
              if (!closed) cont.push_back(branch);
            }
            bool closed = false;
            WithAnte l(this, e->conn.l, &closed);
            return closed? closing(depth) : dfs(depth + 1);
          }
          case IMPLIES: {
            // beta
            branches++;
            WithValue nguard(&branch.numUniversalAbove, numUniversal);
            {
              bool closed = false;
              WithAnte r(this, e->conn.r, &closed);
#ifdef SEMANTIC_BRANCHING
              WithAnte l(this, e->conn.l, &closed);
#endif
              if (!closed) cont.push_back(branch);
            }
            bool closed = false;
            WithSucc n(this, e->conn.l, &closed);
            return closed? closing(depth) : dfs(depth + 1);
          }
          case IFF: {
            // alpha
            const Expr* mp = Expr::make(pool, IMPLIES, e->conn.l, e->conn.r);
            const Expr* mpr = Expr::make(pool, IMPLIES, e->conn.r, e->conn.l);
            bool closed = false;
            WithAnte l(this, mp, &closed);
            WithAnte r(this, mpr, &closed);
            return closed? closing(depth) : dfs(depth);
          }
          case FORALL: {
            // gamma
            bool closed = false;
            size_t id = numUniversal;
            Expr newVar(UNDETERMINED, id); // Disposable (will be copied to `pool` on the next line)
            const Expr* body = e->binder.r->makeReplace(&newVar, pool);
            WithValue n(&numUniversal, numUniversal + 1);
            WithAnte l(this, body, &closed);
            WithAnte r(this, e, &closed, true); // Re-add
            return closed? closing(depth) : dfs(i == γre ? depth + Kγre : depth);
          }
          case EXISTS: {
            // delta
            bool closed = false;
            vector<Expr*> univ;
            for (size_t j = 0; j < numUniversal; j++) univ.push_back(Expr::make(pool, UNDETERMINED, j));
            size_t id = numSkolem + ctx.size();
            Expr newVar(FREE, id, univ); // Disposable (will be copied to `pool` on the next line)
            const Expr* body = e->binder.r->makeReplace(&newVar, pool);
            WithValue n(&numSkolem, numSkolem + 1);
            WithAnte l(this, body, &closed);
            WithAnte r(this, e, &closed);
            return closed? closing(depth) : dfs(depth);
          }
          case UNIQUE: {
            // alpha
            const Expr* exi = Expr::make(pool, EXISTS, e->bv, e->binder.arity, e->binder.sort, e->binder.r);
            const Expr* no2 =
              Expr::make(pool, FORALL, e->bv, e->binder.arity, e->binder.sort,
              Expr::make(pool, IMPLIES, e->binder.r,
              Expr::make(pool, FORALL, e->bv + "'", e->binder.arity, e->binder.sort,
              Expr::make(pool, IMPLIES, e->binder.r,
              Expr::make(pool, FREE, ctx.eq, vector<Expr*>{ Expr::make(pool, BOUND, 1), Expr::make(pool, BOUND, 0) })))));
            bool closed = false;
            WithAnte l(this, exi, &closed);
            WithAnte r(this, no2, &closed);
            return closed? closing(depth) : dfs(depth);
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
    #undef pool

    // We have used up everything...
    return false;
  }

  bool Tableau::search(size_t maxDepth) {
    pools.clear();
    pools.emplace_back();
    cont.clear();
    for (unsigned int i = 0; i < N; i++) {
      branch.indices[i][L] = 0;
      branch.indices[i][R] = 0;
    }
    branch.numUniversalAbove = 0;
    numUniversal = numSkolem = 0;
    maxDepthReached = 0;
    invocations = 0;
    branches = 1;
    backtrackPoints = 0;
    this->maxDepth = maxDepth;
    return dfs(0);
  }

  bool Tableau::iterativeDeepening(size_t maxDepth, size_t step) {
    // Try with smaller depths
    for (size_t i = 1; i < maxDepth; i += step) {
      std::cout << "** Current depth: " << i << std::endl;
      if (search(i)) return true;
    }
    // Try with maximum depth
    std::cout << "** Current depth: " << maxDepth << std::endl;
    return search(maxDepth);
  }

  string Tableau::printState() {
    string res;
    res += "+------------------------------------\n";
    for (unsigned int i = 0; i < N; i++) for (const Expr* e: branch.cedents[i][L])
      res += "| " + e->toString(ctx) + "\n";
    for (unsigned int i = 0; i < N; i++) for (const Expr* e: branch.cedents[i][R])
      res += "| ⊢ " + e->toString(ctx) + "\n";
    res += "+------------------------------------\n";
    return res;
  }

  string Tableau::printStateDebug() {
    string res;
    res += "+------------------------------------\n";
    for (unsigned int i = 0; i < N; i++) {
      res += "| (" + typeToString(i) + ") " + std::to_string(branch.indices[i][L]) + "\n";
      for (const Expr* e: branch.cedents[i][L])
        res += "| " + e->toString(ctx) + "\n";
    }
    for (unsigned int i = 0; i < N; i++) {
      res += "| (" + typeToString(i) + ") " + std::to_string(branch.indices[i][R]) + "\n";
      for (const Expr* e: branch.cedents[i][R])
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
    res += "| Total number of branches: " + std::to_string(branches) + "\n";
    res += "| Total number of backtracking choice points: " + std::to_string(backtrackPoints) + "\n";
    res += "+------------------------------------\n";
    return res;
  }

}
