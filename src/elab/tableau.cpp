#include <algorithm>
#include <iostream>
#include "tableau.hpp"

// #define SEMANTIC_BRANCHING
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
  bool Tableau::applySubs(const Subs& subs) {
    bool res = false;
    for (auto& branch: cont) {
      branch.hashset[L].clear();
      branch.hashset[R].clear();
      for (unsigned int i = 0; i < N; i++) {
        for (auto& e: branch.cedents[i][L]) {
          const Expr* newe = Procs::applySubs(e, subs, pools.back());
          if (*e != *newe) res = true; // DEBUG CODE
          e = newe;
          branch.hashset[L].insert(ExprHash(e));
        }
        for (auto& e: branch.cedents[i][R]) {
          const Expr* newe = Procs::applySubs(e, subs, pools.back());
          if (*e != *newe) res = true; // DEBUG CODE
          e = newe;
          branch.hashset[R].insert(ExprHash(e));
        }
      }
    }
    return res;
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
  class WithCedent {
  public:
    Tableau* const p;
    Tableau::Type i;
    Tableau::Position pos;
    ExprHash ehash;
    bool inserted, reAdd;

    WithCedent(Tableau* p, const Expr* e, Tableau::Position pos, bool* closed, bool reAdd = false):
        p(p), i(Tableau::classify(pos, e)), pos(pos), ehash(ExprHash(e)), inserted(false), reAdd(reAdd) {
      if (reAdd) i = Tableau::Type::γre; // TODO: make least priority
      inserted = p->branch.hashset[pos].insert(ehash).second;
      if (inserted) {
        if (p->branch.hashset[Tableau::invert(pos)].contains(ehash)) {
          *closed = true;
#ifdef PRINT_CLOSURES
          std::cout << "+------------------------------------" << std::endl;
          std::cout << "| Branch closed with:" << std::endl;
          std::cout << "| " << e->toString(p->ctx) << std::endl;
          std::cout << "+------------------------------------" << std::endl;
#endif
        }
      }
      if (inserted || reAdd) p->branch.cedents[i][pos].push_back(e);
    }
    WithCedent(const WithCedent&) = delete;
    WithCedent& operator=(const WithCedent&) = delete;
    ~WithCedent() {
      if (inserted || reAdd) p->branch.cedents[i][pos].pop_back();
      if (inserted) p->branch.hashset[pos].erase(ehash);
    }
  };

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

    auto closing = [this] (size_t depth) {
      if (cont.empty()) return true;
      WithValue s(&branch, cont.back());
      cont.pop_back();
      bool res = dfs(depth);
      cont.push_back(branch);
      return res;
    };

    #define pool pools.back()

    // Iota
    auto iota = [this, closing, depth] (Position pos, const Expr* e) {
      // Try unify and close branch (no need to check for other closures...)
      // TODO: try optimise candidate selection...
      vector<Subs> unifiers;
      for (auto& [q, _]: branch.hashset[invert(pos)]) {
        auto unifier = Procs::unify({{ e, q }}, pool);
        if (unifier.has_value()) {
          if (!Procs::equalAfterSubs(e, q, unifier.value())) throw Unreachable();
#ifdef PRINT_CLOSURES
          std::cout << "+------------------------------------" << std::endl;
          std::cout << "| Branch can be closed with:" << std::endl;
          std::cout << "| " << Procs::applySubs(e, unifier.value(), pool)->toString(ctx) << std::endl;
          std::cout << "+------------------------------------" << std::endl;
#endif
          // Optimization: if there's a unifier that doesn't affect other branches, we use that one and discard the rest.
          if (subsStartsFrom(unifier.value(), branch.numUniversalAbove)) {
            if (applySubs(unifier.value())) throw Unreachable();
            return closing(depth);
          }
          unifiers.push_back(unifier.value());
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
    };

    // Unary alpha
    auto unary = [this, closing, depth] (Position pos, const Expr* e) {
      bool closed = false;
      WithCedent g(this, e, pos, &closed);
      return closed? closing(depth) : dfs(depth);
    };

    // Binary alpha
    auto alpha = [this, closing, depth] (Position pos1, const Expr* e1, Position pos2, const Expr* e2) {
      bool closed = false;
      WithCedent g1(this, e1, pos1, &closed);
      WithCedent g2(this, e2, pos2, &closed);
      return closed? closing(depth) : dfs(depth);
    };

    // Beta
    auto beta = [this, closing, depth] (Position pos1, const Expr* e1, Position pos2, const Expr* e2) {
      // if (dfs(depth)) return true;
      branches++;
      WithValue gn(&branch.numUniversalAbove, numUniversal);
      {
        bool closed = false;
#ifdef SEMANTIC_BRANCHING
        WithCedent g1(this, e1, invert(pos1), &closed);
#endif
        WithCedent g2(this, e2, pos2, &closed);
        if (!closed) cont.push_back(branch);
      }
      bool closed = false;
      WithCedent g(this, e1, pos1, &closed);
      return closed? closing(depth) : dfs(depth + 1);
    };

    using enum Expr::VarTag;

    // Gamma
    auto gamma = [this, closing, depth] (Position pos, const Expr* e, bool reentrant) {
      // if (reentrant && dfs(depth)) return true;
      bool closed = false;
      size_t id = numUniversal;
      Expr newVar(UNDETERMINED, id); // Disposable (will be copied to `pool` on the next line)
      const Expr* body = e->binder.r->makeReplace(&newVar, pool);
      WithValue gn(&numUniversal, numUniversal + 1);
      WithCedent g(this, body, pos, &closed);

      // If `e` contains undetermined variables, it must be a result of some previous application of γ-rule.
      // In this case, the original template is already re-added, so we may avoid re-adding `e` again.
      // (TODO: try delay this to instantiation time?)
      if (e->isGround()) {
        WithCedent gre(this, e, pos, &closed, true); // Re-add
        return closed? closing(depth) : dfs(reentrant? depth + Kγre : depth);
      } else {
        if (reentrant) throw Unreachable();
        return closed? closing(depth) : dfs(depth);
      }
    };

    // Delta
    auto delta = [this, closing, depth] (Position pos, const Expr* e) {
      bool closed = false;
      vector<Expr*> univ;
      for (size_t j = 0; j < numUniversal; j++) univ.push_back(Expr::make(pool, UNDETERMINED, j));
      size_t id = numSkolem + ctx.size();
      Expr newVar(FREE, id, univ); // Disposable (will be copied to `pool` on the next line)
      const Expr* body = e->binder.r->makeReplace(&newVar, pool);
      WithValue gn(&numSkolem, numSkolem + 1);
      WithCedent g(this, body, pos, &closed);
      return closed? closing(depth) : dfs(depth);
    };

    for (unsigned int i: order) {
      using enum Expr::Tag;
      auto&   ante  = branch.cedents[i][L], & succ  = branch.cedents[i][R];
      size_t& antei = branch.indices[i][L], & succi = branch.indices[i][R];

      // Right logical rules (try breaking down one succedent)
      if (succi < succ.size()) {
        const Expr* e = succ[succi];
        WithValue gi(&succi, succi + 1);
        if (!(classify(R, e) == i || classify(R, e) == γ && i == γre)) throw Unreachable();
#ifdef PRINT_TRACE
        std::cout << string(depth * 2, ' ') << "R (" << typeToString(i) << ") " << e->toString(ctx) << std::endl;
#endif
        switch (e->tag) {
          case EMPTY:   return dfs(depth);
          case VAR:     return iota(R, e);
          case TRUE:    return closing(depth);
          case FALSE:   return dfs(depth);
          case NOT:     return unary(L, e->conn.l);
          case AND:     return beta(R, e->conn.l, R, e->conn.r);
          case OR:      return alpha(R, e->conn.l, R, e->conn.r);
          case IMPLIES: return alpha(L, e->conn.l, R, e->conn.r);
          case IFF:     return beta(R, Expr::make(pool, IMPLIES, e->conn.l, e->conn.r),
                                    R, Expr::make(pool, IMPLIES, e->conn.r, e->conn.l));
          case FORALL:  return delta(R, e);
          case EXISTS:  return gamma(R, e, i == γre);
          case UNIQUE:  return beta(R, Expr::make(pool, EXISTS, e->bv, e->binder.arity, e->binder.sort, e->binder.r),
                                    R, Expr::make(pool, FORALL, e->bv, e->binder.arity, e->binder.sort,
                                       Expr::make(pool, IMPLIES, e->binder.r,
                                       Expr::make(pool, FORALL, e->bv + "'", e->binder.arity, e->binder.sort,
                                       Expr::make(pool, IMPLIES, e->binder.r,
                                       Expr::make(pool, FREE, ctx.eq, vector<Expr*>{ Expr::make(pool, BOUND, 1), Expr::make(pool, BOUND, 0) }))))));
          case FORALL2: return dfs(depth); // TODO: second-order δ-rule
          case LAM:     return dfs(depth);
        }
        throw NotImplemented();
      }

      // Left logical rules (try breaking down one antecedent)
      if (antei < ante.size()) {
        const Expr* e = ante[antei];
        WithValue gi(&antei, antei + 1);
        if (!(classify(L, e) == i || classify(L, e) == γ && i == γre)) throw Unreachable();
#ifdef PRINT_TRACE
        std::cout << string(depth * 2, ' ') << "L (" << typeToString(i) << ") " << e->toString(ctx) << std::endl;
#endif
        switch (e->tag) {
          case EMPTY:   return dfs(depth);
          case VAR:     return iota(L, e);
          case TRUE:    return dfs(depth);
          case FALSE:   return closing(depth);
          case NOT:     return unary(R, e->conn.l);
          case AND:     return alpha(L, e->conn.l, L, e->conn.r);
          case OR:      return beta(L, e->conn.l, L, e->conn.r);
          case IMPLIES: return beta(R, e->conn.l, L, e->conn.r);
          case IFF:     return alpha(L, Expr::make(pool, IMPLIES, e->conn.l, e->conn.r),
                                     L, Expr::make(pool, IMPLIES, e->conn.r, e->conn.l));
          case FORALL:  return gamma(L, e, i == γre);
          case EXISTS:  return delta(L, e);
          case UNIQUE:  return alpha(L, Expr::make(pool, EXISTS, e->bv, e->binder.arity, e->binder.sort, e->binder.r),
                                     L, Expr::make(pool, FORALL, e->bv, e->binder.arity, e->binder.sort,
                                        Expr::make(pool, IMPLIES, e->binder.r,
                                        Expr::make(pool, FORALL, e->bv + "'", e->binder.arity, e->binder.sort,
                                        Expr::make(pool, IMPLIES, e->binder.r,
                                        Expr::make(pool, FREE, ctx.eq, vector<Expr*>{ Expr::make(pool, BOUND, 1), Expr::make(pool, BOUND, 0) }))))));
          case FORALL2: return dfs(depth); // "φ" rule is not supported yet...
          case LAM:     return dfs(depth);
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
