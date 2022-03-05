#include <algorithm>
#include <iostream>
#include "tableau.hpp"

#define SEMANTIC_BRANCHING
#define OUTPUT_TRACE
// #define OUTPUT_ON_CLOSURE


namespace Elab {

  using Procs::Subs;

  // Remove dependencies in RHS, and replace all RHS metavariables by those with ID >= `subs.size()`.
  // Could give output of exponential length on certain cases.
  Subs normalizeSubs(Subs subs, Allocator<Expr>& pool) {
    using enum Expr::VarTag;
    size_t nextid = subs.size();
    for (size_t i = 0; i < subs.size(); i++) if (!subs[i]) subs[i] = Expr::make(pool, UNDETERMINED, nextid++);
    for (size_t i = 0; i < subs.size(); i++) subs[i] = Procs::applySubs(subs[i], subs, pool);
    return subs;
  }

  // Restrict a set of closers to metavariables with indices in [0, n).
  // TODO: deduplicate?
  vector<Subs> restrictClosers(vector<Subs> cl, size_t n) {
    for (auto& curr: cl) {
      if (curr.size() > n) curr.resize(n);
      while (!curr.empty() && !curr.back()) curr.pop_back();
      if (curr.empty()) return {{}}; // Shortcut
    }
    return cl;
  }

  // Unify a pair of closers. Metavariables in RHS of `a` and `b` are considered to be disjoint.
  // New metavariables in RHS will have IDs >= (size of the resulting substitution).
  // Pre: `a` and `b` must be normalized.
  // Post: the resulting substitution is normalized.
  // TODO: optimize?
  optional<Subs> unifyClosers(Subs a, Subs b, Allocator<Expr>& pool) {
    using enum Expr::VarTag;
    size_t n = std::max(a.size(), b.size());
    a.resize(n, nullptr);
    b.resize(n, nullptr);

    // Reassign ID to metavariables in the RHS of `a` and `b`.
    vector<optional<size_t>> newid;
    size_t nextid = n;
    auto reassign = [&nextid, &newid] (unsigned int, Expr* x) {
      if (x->var.vartag == UNDETERMINED) {
        while (x->var.id >= newid.size()) newid.push_back(nullopt);
        // x->var.id < newid.size()
        if (!newid[x->var.id].has_value()) newid[x->var.id] = nextid++;
        x->var.id = newid[x->var.id].value();
      }
      return x;
    };
    newid.clear();
    for (auto& e: a) if (e) e = e->updateVars(0, pool, reassign);
    newid.clear();
    for (auto& e: b) if (e) e = e->updateVars(0, pool, reassign);
    // Now the metavariables have IDs >= `n`, and RHS of `a` and `b` have disjoint sets metavariables.

    // Try unify all pairs...
    vector<pair<const Expr*, const Expr*>> eqs;
    for (size_t i = 0; i < n; i++) if (a[i] && b[i]) eqs.emplace_back(a[i], b[i]);
    auto unifier = Procs::unify(eqs, pool);
    if (!unifier.has_value()) return nullopt;

    // Summarize result...
    Subs res;
    for (size_t i = 0; i < n; i++) {
      const Expr* e = a[i]? a[i] : b[i];
      res.push_back(e? Procs::applySubs(e, unifier.value(), pool) : nullptr);
    }
    while(!res.empty() && !res.back()) res.pop_back();
    return res;
  }

  // Unify pairs in a set of closers to obtain another set (the intersection set) of closers.
  // Pre: elements in `as` and `bs` must be normalized.
  // TODO: deduplicate?
  vector<Subs> intersectClosers(const vector<Subs>& as, const vector<Subs>& bs, Allocator<Expr>& pool) {
    // Shortcut
    bool af = false, bf = false;
    for (auto& a: as) if (a.empty()) af = true;
    for (auto& b: as) if (b.empty()) bf = true;
    if (af && bf) return vector<Subs>{{}};
    else if (af) return bs;
    else if (bf) return as;
    // Unify pairs
    vector<Subs> res;
    for (const Subs& a: as) for (const Subs& b: bs) {
      auto unifier = unifyClosers(a, b, pool);
      if (unifier.has_value()) res.push_back(unifier.value());
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
        if (p->hashset[RL].contains(ehash)) {
          *closed = true;
#ifdef OUTPUT_ON_CLOSURE
          std::cout << "+------------------------------------" << std::endl;
          std::cout << "| Branch closed with:" << std::endl;
          std::cout << "| " << e->toString(p->ctx) << std::endl;
          std::cout << "+------------------------------------" << std::endl;
#endif
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
  // Returns the set of closing unifiers, restricted to undetermined variables created above
  // TODO: short-circuit return upon finding a unifier that does not affect other branches
  vector<Subs> Tableau::dfs(size_t depth) {
    #define fail                  vector<Subs>{}
    #define success_unconditional vector<Subs>{{}}

    if (depth >= maxDepth) {
      maxDepthReached = maxDepth;
      return {};
    }
    maxDepthReached = std::max(maxDepthReached, depth);
    invocations++;

    // Tweak parameters here (3/3)
    constexpr static unsigned int order[] = { α, δ, γ, ι, β, γre };
    constexpr static int Kγre = 4; // One reentrant γ-expansion = how many β-expansions?

    for (unsigned int i: order) {
      using enum Expr::Tag;
      using enum Expr::VarTag;
      auto&   ante  = cedents[i][L], & succ  = cedents[i][R];
      size_t& antei = indices[i][L], & succi = indices[i][R];

      // Right logical rules (try breaking down one succedent)
      if (succi < succ.size()) {
        const Expr* e = succ[succi];
        WithValue iguard(&succi, succi + 1);

#ifdef OUTPUT_TRACE
        std::cout << string(depth * 2, ' ') << "F (" << typeToString(i) << ") " << e->toString(ctx) << std::endl;
#endif

        switch (e->tag) {
          case VAR: {
            // iota
            // Try unify and close branch (no need to check for other closures...)
            // TODO: try optimise candidate selection...
            auto res = dfs(depth);
            for (auto& [q, _]: hashset[L]) {
              auto unifier = Procs::unify({{ e, q }}, pool);
              if (unifier.has_value()) {
                if (!Procs::equalAfterSubs(e, q, unifier.value())) throw Unreachable();
                res.push_back(normalizeSubs(unifier.value(), pool));
#ifdef OUTPUT_ON_CLOSURE
                std::cout << "+------------------------------------" << std::endl;
                std::cout << "| Branch can be closed with:" << std::endl;
                std::cout << "| " << Procs::applySubs(e, unifier.value(), pool)->toString(ctx) << std::endl;
                std::cout << "+------------------------------------" << std::endl;
#endif
              }
            }
            return res;
          }
          case TRUE:
#ifdef OUTPUT_ON_CLOSURE
            std::cout << "Branch closed with true at succedent" << std::endl;
#endif
            return success_unconditional;
          case FALSE:
            return dfs(depth);
          case NOT: {
            bool closed = false;
            WithAnte n(this, e->conn.l, &closed);
            return closed? success_unconditional : dfs(depth);
          }
          case AND: {
            // beta
            vector<Subs> lcl, rcl;
            {
              bool closed = false;
              WithSucc l(this, e->conn.l, &closed);
              lcl = closed? success_unconditional : dfs(depth + 1);
            }
            branches++;
            {
              bool closed = false;
              WithSucc r(this, e->conn.r, &closed);
#ifdef SEMANTIC_BRANCHING
              WithAnte l(this, e->conn.l, &closed);
#endif
              rcl = closed? success_unconditional : dfs(depth + 1);
            }
            return intersectClosers(lcl, rcl, pool);
          }
          case OR: {
            // alpha
            bool closed = false;
            WithSucc l(this, e->conn.l, &closed);
            WithSucc r(this, e->conn.r, &closed);
            return closed? success_unconditional : dfs(depth);
          }
          case IMPLIES: {
            // alpha
            bool closed = false;
            WithAnte l(this, e->conn.l, &closed);
            WithSucc r(this, e->conn.r, &closed);
            return closed? success_unconditional : dfs(depth);
          }
          case IFF: {
            // beta
            vector<Subs> lcl, rcl;
            Expr mp(IMPLIES, e->conn.l, e->conn.r);
            Expr mpr(IMPLIES, e->conn.r, e->conn.l);
            {
              bool closed = false;
              WithSucc l(this, &mp, &closed);
              lcl = closed? success_unconditional : dfs(depth + 1);
            }
            branches++;
            {
              bool closed = false;
              WithSucc r(this, &mpr, &closed);
#ifdef SEMANTIC_BRANCHING
              WithAnte l(this, &mp, &closed);
#endif
              rcl = closed? success_unconditional : dfs(depth + 1);
            }
            return intersectClosers(lcl, rcl, pool);
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
            return closed? success_unconditional : dfs(depth);
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
            auto res = dfs(i == γre ? depth + Kγre : depth);
            return closed? success_unconditional : restrictClosers(res, id);
          }
          case UNIQUE: {
            // beta
            vector<Subs> lcl, rcl;
            Expr exi(EXISTS, e->bv, e->binder.arity, e->binder.sort, e->binder.r);
            {
              bool closed = false;
              WithSucc l(this, &exi, &closed);
              lcl = closed? success_unconditional : dfs(depth + 1);
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
              rcl = closed? success_unconditional : dfs(depth + 1);
            }
            return intersectClosers(lcl, rcl, pool);
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

#ifdef OUTPUT_TRACE
        std::cout << string(depth * 2, ' ') << "T (" << typeToString(i) << ") " << e->toString(ctx) << std::endl;
#endif

        switch (e->tag) {
          case VAR: {
            // iota
            // Try unify and close branch (no need to check for other closures...)
            // TODO: try optimise candidate selection...
            auto res = dfs(depth);
            for (auto& [q, _]: hashset[R]) {
              auto unifier = Procs::unify({{ e, q }}, pool);
              if (unifier.has_value()) {
                if (!Procs::equalAfterSubs(e, q, unifier.value())) throw Unreachable();
                res.push_back(normalizeSubs(unifier.value(), pool));
#ifdef OUTPUT_ON_CLOSURE
                std::cout << "+------------------------------------" << std::endl;
                std::cout << "| Branch can be closed with:" << std::endl;
                std::cout << "| " << Procs::applySubs(e, unifier.value(), pool)->toString(ctx) << std::endl;
                std::cout << "+------------------------------------" << std::endl;
#endif
              }
            }
            return res;
          }
          case TRUE:
            return dfs(depth);
          case FALSE:
#ifdef OUTPUT_ON_CLOSURE
            std::cout << "Branch closed with false at antecedent" << std::endl;
#endif
            return success_unconditional;
          case NOT: {
            bool closed = false;
            WithSucc n(this, e->conn.l, &closed);
            return closed? success_unconditional : dfs(depth);
          }
          case AND: {
            // alpha
            bool closed = false;
            WithAnte l(this, e->conn.l, &closed);
            WithAnte r(this, e->conn.r, &closed);
            return closed? success_unconditional : dfs(depth);
          }
          case OR: {
            // beta
            vector<Subs> lcl, rcl;
            {
              bool closed = false;
              WithAnte l(this, e->conn.l, &closed);
              lcl = closed? success_unconditional : dfs(depth + 1);
            }
            branches++;
            {
              bool closed = false;
              WithAnte r(this, e->conn.r, &closed);
#ifdef SEMANTIC_BRANCHING
              WithSucc l(this, e->conn.l, &closed);
#endif
              rcl = closed? success_unconditional : dfs(depth + 1);
            }
            return intersectClosers(lcl, rcl, pool);
          }
          case IMPLIES: {
            // beta
            vector<Subs> lcl, rcl;
            {
              bool closed = false;
              WithSucc n(this, e->conn.l, &closed);
              lcl = closed? success_unconditional : dfs(depth + 1);
            }
            branches++;
            {
              bool closed = false;
              WithAnte r(this, e->conn.r, &closed);
#ifdef SEMANTIC_BRANCHING
              WithAnte l(this, e->conn.l, &closed);
#endif
              rcl = closed? success_unconditional : dfs(depth + 1);
            }
            return intersectClosers(lcl, rcl, pool);
          }
          case IFF: {
            // alpha
            Expr mp(IMPLIES, e->conn.l, e->conn.r);
            Expr mpr(IMPLIES, e->conn.r, e->conn.l);
            bool closed = false;
            WithAnte l(this, &mp, &closed);
            WithAnte r(this, &mpr, &closed);
            return closed? success_unconditional : dfs(depth);
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
            auto res = dfs(i == γre ? depth + Kγre : depth);
            return closed? success_unconditional : restrictClosers(res, id);
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
            return closed? success_unconditional : dfs(depth);
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
            return closed? success_unconditional : dfs(depth);
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

    // We have used up everything...
    return fail;
    #undef fail
    #undef success_unconditional
  }

  bool Tableau::search(size_t maxDepth) {
    for (unsigned int i = 0; i < N; i++) {
      indices[i][L] = 0;
      indices[i][R] = 0;
    }
    numUniversal = numSkolem = 0;
    maxDepthReached = 0;
    invocations = 0;
    branches = 1;
    this->maxDepth = maxDepth;
    auto res = dfs(0);
    std::cout << res.size() << std::endl;
    return !res.empty();
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
    res += "| Total number of branches: " + std::to_string(branches) + "\n";
    res += "+------------------------------------\n";
    return res;
  }

}
