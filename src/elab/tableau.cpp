#include <algorithm>
#include <iostream>
#include <sstream>
#include <fstream>
#include <random>
#include "tableau.hpp"

#define SEMANTIC_BRANCHING
// #define CHECK_INVARIANTS
// #define DEBUG_TRACE

namespace Elab {

  using Procs::Subs;

  std::random_device rd;
  std::mt19937 e{ rd() };

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
    #pragma GCC diagnostic push
    #pragma GCC diagnostic ignored "-Wterminate"
    throw NotImplemented();
    #pragma GCC diagnostic pop
  }

  // Apply `subs` to all of `cont`
  void Tableau::applySubs(const Subs& subs, [[maybe_unused]] bool assertNoChange) {
    for (size_t ind = 0; ind < cont.size(); ind++) {
      auto& branch = cont[ind];
      branch.hashset[L].clear();
      branch.hashset[R].clear();
      for (unsigned int i = 0; i < N; i++) {
        for (auto& e: branch.cedents[i][L]) {
          const Expr* newe = Procs::applySubs(e, subs, pools.back());
#ifdef CHECK_INVARIANTS
          if (assertNoChange && *e != *newe) {
            std::cout << "Assertion failed at alt branch " << std::to_string(ind) << ":" << std::endl;
            std::cout << "Branch has numUniversal = " << branch.numUniversal << std::endl;
            std::cout << "But formula in L (" << typeToString(i) << ") is modified:" << std::endl;
            std::cout << "Old: " << e->toString(ctx) << std::endl;
            std::cout << "New: " << newe->toString(ctx) << std::endl;
            debughtml("crash");
            throw Unreachable();
          }
#endif
          e = newe;
          branch.numUniversal = std::max(branch.numUniversal, e->numUndetermined());
          branch.hashset[L].insert(ExprHash(e));
        }
        for (auto& e: branch.cedents[i][R]) {
          const Expr* newe = Procs::applySubs(e, subs, pools.back());
#ifdef CHECK_INVARIANTS
          if (assertNoChange && *e != *newe) {
            std::cout << "Assertion failed at alt branch " << std::to_string(ind) << ":" << std::endl;
            std::cout << "Branch has numUniversal = " << branch.numUniversal << std::endl;
            std::cout << "But formula in R (" << typeToString(i) << ") is modified:" << std::endl;
            std::cout << "Old: " << e->toString(ctx) << std::endl;
            std::cout << "New: " << newe->toString(ctx) << std::endl;
            debughtml("crash");
            throw Unreachable();
          }
#endif
          e = newe;
          branch.numUniversal = std::max(branch.numUniversal, e->numUndetermined());
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
  class WithCedent {
  public:
    Tableau* const p;
    Tableau::Type i;
    Tableau::Position pos;
    ExprHash ehash;
    bool inserted, reAdd;

    WithCedent(Tableau* p, const Expr* e, Tableau::Position pos, bool* closed, bool reAdd = false):
        p(p), i(Tableau::classify(pos, e)), pos(pos), ehash(ExprHash(e)), inserted(false), reAdd(reAdd) {
      if (reAdd) i = Tableau::Type::γre;
      inserted = p->branch.hashset[pos].insert(ehash).second;
      if (inserted) { // TODO: remove if
        if (p->branch.hashset[Tableau::invert(pos)].contains(ehash)) *closed = true;
      }
      if (inserted || reAdd) {
        p->branch.cedents[i][pos].push_back(e);
        p->branch.timestamps[i][pos].push_back(p->branch.numCedents);
        p->branch.numCedents++;
        p->branch.numUniversals[i][pos].push_back(p->branch.numUniversal);
        if (i == Tableau::Type::β) p->branch.betaUsed[pos].push_back(false);
      }
    }
    WithCedent(const WithCedent&) = delete;
    WithCedent& operator=(const WithCedent&) = delete;
    ~WithCedent() {
      if (inserted || reAdd) {
        p->branch.cedents[i][pos].pop_back();
        p->branch.timestamps[i][pos].pop_back();
        p->branch.numCedents--;
        p->branch.numUniversals[i][pos].pop_back();
        if (i == Tableau::Type::β) p->branch.betaUsed[pos].pop_back();
      }
      if (inserted) p->branch.hashset[pos].erase(ehash);
    }
  };

  // Pre: all elements of `ante`, `succ`, `anteSet` and `succSet` are valid, well-formed formulas
  // All states will be unmodified/restored
  bool Tableau::dfs(size_t depth) {
    check();

    // TODO: make early test in branching situations
    if (branch.depth >= maxTabDepth) {
      return false;
    }
    if (depth >= maxDepth) {
      maxDepthReached = maxDepth;
      return false;
    }
    maxDepthReached = std::max(maxDepthReached, depth);
    invocations++;

#ifdef DEBUG_TRACE
    if (invocations % 1000 == 0) {
      debughtml("log_" + std::to_string(invocations));
    }
#endif

    auto closing = [this] (size_t depth) {
      if (cont.empty()) return true;
      Branch backup = branch;
      branch = cont.back(); cont.pop_back();
#ifdef CHECK_INVARIANTS
      Branch t = branch;
#endif
      bool res = dfs(depth);
#ifdef CHECK_INVARIANTS
      if (branch != t) throw Unreachable();
#endif
      cont.push_back(branch);
      branch = backup;
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
          // Optimization: if there's a unifier that doesn't affect other branches, we use that one and discard the rest.
          if (cont.empty() || subsStartsFrom(unifier.value(), cont.back().numUniversal)) {
            vector<Branch> backup = cont;
            pools.emplace_back();
            applySubs(unifier.value(), true);
#ifdef CHECK_INVARIANTS
            vector<Branch> t = cont;
#endif
            bool res = closing(depth);
#ifdef CHECK_INVARIANTS
            if (cont != t) throw Unreachable();
#endif
            cont = backup;
            pools.pop_back();
            return res; // We could not expect better outcomes!
          }
          unifiers.push_back(unifier.value());
        }
      }
      if (!unifiers.empty()) {
        backtrackPoints++;
        vector<Branch> backup = cont;
        for (const Subs& unifier: unifiers) {
          pools.emplace_back();
          applySubs(unifier, false);
#ifdef CHECK_INVARIANTS
          vector<Branch> t = cont;
#endif
          bool res = closing(depth);
#ifdef CHECK_INVARIANTS
          if (cont != t) throw Unreachable();
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
      if (e1->size() >= e2->size()) {
        std::swap(pos1, pos2);
        std::swap(e1, e2);
      }
      // e1->size() < e2->size()
#ifdef CHECK_INVARIANTS
      vector<Branch> t = cont;
#endif
      bool inserted = false;
      {
        bool closed = false;
#ifdef SEMANTIC_BRANCHING
        WithCedent g1(this, e1, invert(pos1), &closed);
#endif
        WithCedent g2(this, e2, pos2, &closed);
        WithValue gd(&branch.depth, branch.depth + 1);
        if (!closed) {
          cont.push_back(branch);
          inserted = true;
        }
      }
      bool closed = false;
      WithCedent g(this, e1, pos1, &closed);
      WithValue gd(&branch.depth, closed? branch.depth : (branch.depth + 1));
      bool res = closed? closing(depth) : dfs(depth + 1);
      if (inserted) cont.pop_back();
#ifdef CHECK_INVARIANTS
      if (cont != t) throw Unreachable();
#endif
      return res;
    };

    using enum Expr::Tag;
    using enum Expr::VarTag;

    // Gamma
    auto gamma = [this, closing, depth] (Position pos, const Expr* e, bool reentrant) {
      // TODO: selection in reentrant gamma expansions
      bool closed = false;
      size_t id = branch.numUniversal;
      Expr newVar(UNDETERMINED, id); // Disposable (will be copied to `pool` on the next line)
      const Expr* body = e->binder.r->makeReplace(&newVar, pool);
      WithValue gn(&branch.numUniversal, branch.numUniversal + 1);
      WithCedent g(this, body, pos, &closed);

      // If `e` contains undetermined variables, it must be a result of some previous application of γ-rule.
      // In this case, the original template is already re-added, so we may avoid re-adding `e` again.
      // (TODO: try delay this to instantiation time?)
      if (e->isGround()) {
        WithCedent gre(this, e, pos, &closed, true); // Re-add
        WithValue gd(&branch.depth, closed? branch.depth : reentrant ? (branch.depth + 1) : branch.depth);
        return closed? closing(depth) : dfs(reentrant? (depth + 1) : depth);
      } else {
        if (reentrant) throw Unreachable();
        return closed? closing(depth) : dfs(depth);
      }
    };

    // Delta
    auto delta = [this, closing, depth] (Position pos, const Expr* e) {
      bool closed = false;
      vector<Expr*> univ;
      for (size_t j = 0; j < branch.numUniversal; j++) univ.push_back(Expr::make(pool, UNDETERMINED, j));
      size_t id = numSkolem + ctx.size();
      Expr newVar(FREE, id, univ); // Disposable (will be copied to `pool` on the next line)
      const Expr* body = e->binder.r->makeReplace(&newVar, pool);
      WithValue gn(&numSkolem, numSkolem + 1);
      WithCedent g(this, body, pos, &closed);
      return closed? closing(depth) : dfs(depth);
    };

    // Tweak parameters here (3/3)
    constexpr static unsigned int order[] = { ι, α, δ, γ, /* β, γre */ };

    for (unsigned int i: order) {
      auto&   ante  = branch.cedents[i][L], & succ  = branch.cedents[i][R];
      size_t& antei = branch.indices[i][L], & succi = branch.indices[i][R];

      // Left logical rules (try breaking down one antecedent)
      if (antei < ante.size()) {
        const Expr* e = ante[antei];
        WithValue gi(&antei, antei + 1);
        if (!(classify(L, e) == i || (classify(L, e) == γ && i == γre))) throw Unreachable();
        switch (e->tag) {
          case EMPTY:   return dfs(depth);
          case VAR:     return iota(L, e);
          case TRUE:    return dfs(depth);
          case FALSE:   return closing(depth);
          case NOT:     return unary(R, e->conn.l);
          case AND:     return alpha(L, e->conn.l, L, e->conn.r);
          case OR:      throw Unreachable();
          case IMPLIES: throw Unreachable();
          case IFF:     return alpha(L, Expr::make(pool, IMPLIES, e->conn.l, e->conn.r),
                                     L, Expr::make(pool, IMPLIES, e->conn.r, e->conn.l));
          case FORALL:  return gamma(L, e, false);
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
        throw Unreachable();
      }

      // Right logical rules (try breaking down one succedent)
      if (succi < succ.size()) {
        const Expr* e = succ[succi];
        WithValue gi(&succi, succi + 1);
        if (!(classify(R, e) == i || (classify(R, e) == γ && i == γre))) throw Unreachable();
        switch (e->tag) {
          case EMPTY:   return dfs(depth);
          case VAR:     return iota(R, e);
          case TRUE:    return closing(depth);
          case FALSE:   return dfs(depth);
          case NOT:     return unary(L, e->conn.l);
          case AND:     throw Unreachable();
          case OR:      return alpha(R, e->conn.l, R, e->conn.r);
          case IMPLIES: return alpha(L, e->conn.l, R, e->conn.r);
          case IFF:     throw Unreachable();
          case FORALL:  return delta(R, e);
          case EXISTS:  return gamma(R, e, false);
          case UNIQUE:  throw Unreachable();
          case FORALL2: return dfs(depth); // TODO: second-order δ-rule
          case LAM:     return dfs(depth);
        }
        throw Unreachable();
      }
    }

    // We have used up everything except β and γre...

    // The relative order of β's does make a difference...
    // So I have to use a separate `betaUsed` mechanism...
    // TODO: sort by complexity?
    if (branch.depth < maxTabDepth) {
      unsigned int i = β;
      auto&   ante  = branch.cedents[i][L], & succ  = branch.cedents[i][R];
      // size_t& antei = branch.indices[i][L], & succi = branch.indices[i][R];
      auto&   anteu = branch.betaUsed[L],   & succu = branch.betaUsed[R];

      for (size_t ii = 0; ii < ante.size(); ii++) if (!anteu[ii]) {
        const Expr* e = ante[ii];
        anteu[ii] = true;
        bool res = false;
        switch (e->tag) {
          case OR:      res = beta(L, e->conn.l, L, e->conn.r); break;
          case IMPLIES: res = beta(R, e->conn.l, L, e->conn.r); break;
          default:      throw Unreachable();
        }
        anteu[ii] = false;
        if (res) return true;
      }
      for (size_t ii = 0; ii < succ.size(); ii++) if (!succu[ii]) {
        const Expr* e = succ[ii];
        // Ahhhhhhh this is too messy
        succu[ii] = true;
        bool res = false;
        switch (e->tag) {
          case AND:
            res = beta(R, e->conn.l, R, e->conn.r);
            break;
          case IFF:
            res = beta(R, Expr::make(pool, IMPLIES, e->conn.l, e->conn.r),
                       R, Expr::make(pool, IMPLIES, e->conn.r, e->conn.l));
            break;
          case UNIQUE:
            res = beta(R, Expr::make(pool, EXISTS, e->bv, e->binder.arity, e->binder.sort, e->binder.r),
                       R, Expr::make(pool, FORALL, e->bv, e->binder.arity, e->binder.sort,
                          Expr::make(pool, IMPLIES, e->binder.r,
                          Expr::make(pool, FORALL, e->bv + "'", e->binder.arity, e->binder.sort,
                          Expr::make(pool, IMPLIES, e->binder.r,
                          Expr::make(pool, FREE, ctx.eq, vector<Expr*>{ Expr::make(pool, BOUND, 1), Expr::make(pool, BOUND, 0) }))))));
            break;
          default:
            throw Unreachable();
        }
        succu[ii] = false;
        if (res) return true;
      }
    }

    // The relative order of γ's are unimportant, so we could proceed with the insertion order
    if (branch.depth < maxTabDepth) {
      unsigned int i = γre;
      auto&   ante  = branch.cedents[i][L], & succ  = branch.cedents[i][R];
      size_t& antei = branch.indices[i][L], & succi = branch.indices[i][R];

      for (size_t ii = antei; ii < ante.size(); ii++) {
        const Expr* e = ante[ii];
        WithValue gi(&antei, ii + 1);
        switch (e->tag) {
          case FORALL:  if (gamma(L, e, true)) return true; break;
          default:      throw Unreachable();
        }
      }
      for (size_t ii = succi; ii < succ.size(); ii++) {
        const Expr* e = succ[ii];
        WithValue gi(&succi, ii + 1);
        switch (e->tag) {
          case EXISTS:  if (gamma(R, e, true)) return true; break;
          default:      throw Unreachable();
        }
      }
    }

    #undef pool

    // We have used up everything now...
    return false;
  }

  bool Tableau::search(size_t maxDepth, size_t maxTabDepth) {
    pools.clear();
    pools.emplace_back();
    cont.clear();
    for (unsigned int i = 0; i < N; i++) {
      branch.indices[i][L] = 0;
      branch.indices[i][R] = 0;
    }
    branch.depth = 0;
    branch.numUniversal = 0;
    numSkolem = 0;
    maxDepthReached = 0;
    invocations = 0;
    branches = 1;
    backtrackPoints = 0;
    this->maxDepth = maxDepth;
    this->maxTabDepth = maxTabDepth;
    return dfs(0);
  }

  bool Tableau::iterativeDeepening(size_t maxTabDepth, size_t step) {
    // Try with smaller depths
    size_t maxDepth = 2;
    for (size_t i = 1; i < maxTabDepth; i += step, maxDepth += step * 4) {
      std::cout << "** Current tableau depth: " << i << ", search depth: " << maxDepth << ", ";
      bool res = search(maxDepth, i);
      std::cout << "DFS invocations: " << invocations << std::endl;
      if (res) return true;
    }
    // Try with maximum depth
    std::cout << "** Current tableau depth: " << maxTabDepth << ", search depth: " << maxDepth << ", ";
    bool res = search(maxDepth, maxTabDepth);
    std::cout << "DFS invocations: " << invocations << std::endl;
    return res;
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
    res += "| Maximum search depth: " + std::to_string(maxDepthReached) + "\n";
    res += "| Total number of backtracking choice points: " + std::to_string(backtrackPoints) + "\n";
    res += "+------------------------------------\n";
    return res;
  }

  void Tableau::checkBranch(const Branch& b) {
    unordered_set<ExprHash, ExprHash::GetHash> ths[2] = { b.hashset[0], b.hashset[1] };
    for (unsigned int i = 0; i < N; i++) {
      for (unsigned int pos = 0; pos < 2; pos++) {
        for (const Expr* e: b.cedents[i][pos]) {
          if (!ths[pos].contains(ExprHash(e))) {
            std::cout << "Assertion failed: inconsistent state, formula" << std::endl;
            std::cout << "    " << e->toString(ctx) << std::endl;
            std::cout << "not found in hashset." << std::endl;
            throw Unreachable();
          }
        }
      }
    }
    for (unsigned int i = 0; i < N; i++) {
      for (unsigned int pos = 0; pos < 2; pos++) {
        for (const Expr* e: b.cedents[i][pos]) {
          ths[pos].erase(ExprHash(e));
        }
      }
    }
    for (const ExprHash& eh: ths[0]) {
      std::cout << "Assertion failed: inconsistent state, formula" << std::endl;
      std::cout << "    " << eh.e->toString(ctx) << std::endl;
      std::cout << "not found in cedents." << std::endl;
      throw Unreachable();
    }
    for (const ExprHash& eh: ths[1]) {
      std::cout << "Assertion failed: inconsistent state, formula" << std::endl;
      std::cout << "    " << eh.e->toString(ctx) << std::endl;
      std::cout << "not found in cedents." << std::endl;
      throw Unreachable();
    }
  }

  void Tableau::check() {
#ifdef CHECK_INVARIANTS
    checkBranch(branch);
    for (size_t ind = 0; ind < cont.size(); ind++) {
      const Branch& branch = cont[ind];
      checkBranch(branch);
      if (branch.cedents[β][L].size() != branch.betaUsed[L].size()) throw Unreachable();
      if (branch.cedents[β][R].size() != branch.betaUsed[R].size()) throw Unreachable();
      for (unsigned int i = 0; i < N; i++) {
        if (branch.cedents[i][L].size() != branch.timestamps[i][L].size()) throw Unreachable();
        if (branch.cedents[i][L].size() != branch.numUniversals[i][L].size()) throw Unreachable();
        for (const Expr* e: branch.cedents[i][L]) {
          if (e->numUndetermined() > branch.numUniversal) {
            std::cout << "Assertion failed at alt branch " << std::to_string(ind) << ":" << std::endl;
            std::cout << "Branch has numUniversal = " << branch.numUniversal << std::endl;
            std::cout << "But formula in L (" << typeToString(i) << ") has more:" << std::endl;
            std::cout << "    " << e->toString(ctx) << std::endl;
            debughtml("crash");
            throw Unreachable();
          }
        }
        if (branch.cedents[i][R].size() != branch.timestamps[i][R].size()) throw Unreachable();
        if (branch.cedents[i][R].size() != branch.numUniversals[i][R].size()) throw Unreachable();
        for (const Expr* e: branch.cedents[i][R]) {
          if (e->numUndetermined() > branch.numUniversal) {
            std::cout << "Assertion failed at alt branch " << std::to_string(ind) << ":" << std::endl;
            std::cout << "Branch has numUniversal = " << branch.numUniversal << std::endl;
            std::cout << "But formula in R (" << typeToString(i) << ") has more:" << std::endl;
            std::cout << "    " << e->toString(ctx) << std::endl;
            debughtml("crash");
            throw Unreachable();
          }
        }
      }
    }
#endif
  }

  void Tableau::debughtml(const string& filename) {
    using std::endl;
    std::ofstream out(filename + ".html");

    out <<
      "<head><style>"
      "  table td, table td * { vertical-align: top; }"
      "  .disabled { color: #bbbbbb; }"
      "</style></head><body>";
    out << "<h1>Debug info</h1>";
    out << "<p>Number of branches: " << cont.size() + 1 << "</p>";
    out << "<p>Number of Skolem vars: " << numSkolem << "</p>";
    out << "<p>Maximum search depth: " << maxDepth << "</p>";
    out << "<p>Maximum beta-depth: " << maxTabDepth << "</p>";

    out << "<table><tbody><tr>";
    auto printBranch = [this, &out] (const Branch& b, const string& name) {
      struct Item {
        size_t timestamp;
        unsigned int pos, type;
        bool active;
        size_t numUniversal;
        const Expr* e;
        auto operator<=>(const Item&) const = default;
      };

      out << "<td style=\"border: 1px solid black; padding: 10px; width: 480px;\">";
      out << "<h2>Branch " << name << ":</h2>";
      out << "<p>Number of cedents: " << b.numCedents << "</p>";
      out << "<p>Branch beta-depth: " << b.depth << "</p>";
      out << "<p>Number of universals: " << b.numUniversal << "</p>";

      vector<Item> a;
      for (unsigned int i = 0; i < N; i++) {
        for (size_t j = 0; j < b.cedents[i][L].size(); j++) {
          bool active = (i == β? !b.betaUsed[L][j] : j >= b.indices[i][L]);
          a.emplace_back(b.timestamps[i][L][j], L, i, active, b.numUniversals[i][L][j], b.cedents[i][L][j]);
        }
        for (size_t j = 0; j < b.cedents[i][R].size(); j++) {
          bool active = (i == β? !b.betaUsed[R][j] : j >= b.indices[i][R]);
          a.emplace_back(b.timestamps[i][R][j], R, i, active, b.numUniversals[i][R][j], b.cedents[i][R][j]);
        }
      }
      sort(a.begin(), a.end());

      out << "<p><b>Antecedents and succedents:</b></p>";
      for (auto& [ts, pos, type, active, numUniversal, e]: a) {
        out << "<p " << (active ? "" : "class=\"disabled\"") << ">";
        out << "<code>" << (pos == L? "L" : "R") << " (" << typeToString(type) << ") ";
        out << e->toString(ctx) << "</code>";
        out << "<br /><sup>" << ts << "/" << numUniversal << "</sup>";
        out << "</p>";
      }
      out << "</td>";
    };
    printBranch(branch, "main");
    for (size_t i = 0; i < cont.size(); i++) {
      printBranch(cont[cont.size() - 1 - i], std::to_string(i));
    }
    out << "</tr></tbody></table></body>" << endl;
  }

}
