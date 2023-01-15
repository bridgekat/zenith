#include "tableau.hpp"
#include <algorithm>
#include <fstream>
#include <iostream>
#include <sstream>

#define SEMANTIC_BRANCHING
// #define CHECK_INVARIANTS
// #define DEBUG_TRACE

namespace Elab {

  using Procs::Subs;

  // std::random_device rd;
  // std::mt19937 e{ rd() };

  // Simple case: disjoint
  /*
  Subs simpleCompose(Subs const& a, Subs const& b) noexcept {
    Subs res(std::max(a.size(), b.size()), nullptr);
    for (size_t i = 0; i < res.size(); i++) {
      bool af = i < a.size() && a[i], bf = i < b.size() && b[i];
      if (af && bf) unreachable;
      res[i] = af ? a[i] : bf ? b[i] : nullptr;
    }
    return res;
  }
  */

  string typeToString(unsigned int t) noexcept {
    using enum Tableau::Type;
    switch (t) {
      case Iota: return "ι";
      case Alpha: return "α";
      case Beta: return "β";
      case Gamma: return "γ";
      case Delta: return "δ";
      case GammaRe: return "γre";
    }
    return "?";
  }

  Tableau::Type Tableau::classify(Position antesucc, Expr const* e) noexcept {
    using enum FOLForm::Tag;
    auto fof = FOLForm::fromExpr(e);
    switch (antesucc) {
      case L:
        switch (fof.tag) {
          case Other: return Iota;
          case Equals: return Iota;
          case True: return Alpha;
          case False: return Alpha;
          case Not: return Alpha;
          case And: return Alpha;
          case Or: return Beta;
          case Implies: return Beta;
          case Iff: return Alpha;
          case Forall: return Gamma;
          case Exists: return Delta;
          case Unique: return Alpha;
        }
        break;
      case R:
        switch (fof.tag) {
          case Other: return Iota;
          case Equals: return Iota;
          case True: return Alpha;
          case False: return Alpha;
          case Not: return Alpha;
          case And: return Beta;
          case Or: return Alpha;
          case Implies: return Alpha;
          case Iff: return Beta;
          case Forall: return Delta;
          case Exists: return Gamma;
          case Unique: return Beta;
        }
        break;
    }
    unreachable;
  }

  // Apply `subs` to all of `cont`
  void Tableau::applySubs(Subs const& subs, [[maybe_unused]] bool assertNoChange) {
    for (size_t ind = 0; ind < cont.size(); ind++) {
      auto& branch = cont[ind];
      branch.hashset[L].clear();
      branch.hashset[R].clear();
      for (unsigned int i = 0; i < N; i++) {
        for (auto& e: branch.cedents[i][L]) {
          Expr const* newe = Procs::applySubs(e, subs, pools.back());
#ifdef CHECK_INVARIANTS
          if (assertNoChange && *e != *newe) {
            std::cout << "Assertion failed at alt branch " << std::to_string(ind) << ":" << std::endl;
            std::cout << "Branch has numUniversal = " << branch.numUniversal << std::endl;
            std::cout << "But formula in L (" << typeToString(i) << ") is modified:" << std::endl;
            std::cout << "Old: " << e->toString(ctx) << std::endl;
            std::cout << "New: " << newe->toString(ctx) << std::endl;
            debughtml("crash");
            unreachable;
          }
#endif
          e = newe;
          branch.numUniversal = std::max(branch.numUniversal, e->numMeta());
          branch.hashset[L].insert(ExprHash(e));
        }
        for (auto& e: branch.cedents[i][R]) {
          Expr const* newe = Procs::applySubs(e, subs, pools.back());
#ifdef CHECK_INVARIANTS
          if (assertNoChange && *e != *newe) {
            std::cout << "Assertion failed at alt branch " << std::to_string(ind) << ":" << std::endl;
            std::cout << "Branch has numUniversal = " << branch.numUniversal << std::endl;
            std::cout << "But formula in R (" << typeToString(i) << ") is modified:" << std::endl;
            std::cout << "Old: " << e->toString(ctx) << std::endl;
            std::cout << "New: " << newe->toString(ctx) << std::endl;
            debughtml("crash");
            unreachable;
          }
#endif
          e = newe;
          branch.numUniversal = std::max(branch.numUniversal, e->numMeta());
          branch.hashset[R].insert(ExprHash(e));
        }
      }
    }
  }

  // Check if `subs` does not contain variables with ID less than `offset`
  bool subsStartsFrom(Subs const& subs, size_t offset) {
    for (size_t i = 0; i < subs.size() && i < offset; i++)
      if (subs[i]) return false;
    return true;
  }

  // Scope guard for "change value, recurse, and change back"
  template <typename T>
  class WithValue {
  public:
    T* const p;
    T const prev;
    WithValue(T* p, T const& value): p(p), prev(*p) { *p = value; }
    WithValue(WithValue const&) = delete;
    WithValue& operator=(WithValue const&) = delete;
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

    WithCedent(Tableau* p, Expr const* e, Tableau::Position pos, bool* closed, bool reAdd = false):
      p(p), i(Tableau::classify(pos, e)), pos(pos), ehash(ExprHash(e)), inserted(false), reAdd(reAdd) {
      if (reAdd) i = Tableau::Type::GammaRe;
      inserted = p->branch.hashset[pos].insert(ehash).second;
      if (p->branch.hashset[Tableau::invert(pos)].contains(ehash)) *closed = true;
      if (inserted || reAdd) {
        p->branch.cedents[i][pos].push_back(e);
        p->branch.timestamps[i][pos].push_back(p->branch.numCedents);
        p->branch.numCedents++;
        p->branch.numUniversals[i][pos].push_back(p->branch.numUniversal);
        if (i == Tableau::Type::Beta) p->branch.betaUsed[pos].push_back(false);
      }
    }
    WithCedent(WithCedent const&) = delete;
    WithCedent& operator=(WithCedent const&) = delete;
    ~WithCedent() {
      if (inserted || reAdd) {
        p->branch.cedents[i][pos].pop_back();
        p->branch.timestamps[i][pos].pop_back();
        p->branch.numCedents--;
        p->branch.numUniversals[i][pos].pop_back();
        if (i == Tableau::Type::Beta) p->branch.betaUsed[pos].pop_back();
      }
      if (inserted) p->branch.hashset[pos].erase(ehash);
    }
  };

  // All states will be unmodified/restored
  bool Tableau::dfs(size_t depth) {
    check();

    // TODO: make early test in branching situations
    if (branch.depth >= maxTabDepth) { return false; }
    if (depth >= maxDepth) {
      maxDepthReached = maxDepth;
      return false;
    }
    maxDepthReached = std::max(maxDepthReached, depth);
    invocations++;

#ifdef DEBUG_TRACE
    if (invocations % 1000 == 0) { debughtml("log_" + std::to_string(invocations)); }
#endif

    auto closing = [this](size_t depth) {
      if (cont.empty()) return true;
      Branch backup = branch;
      branch = cont.back();
      cont.pop_back();
#ifdef CHECK_INVARIANTS
      Branch t = branch;
#endif
      bool res = dfs(depth);
#ifdef CHECK_INVARIANTS
      if (branch != t) unreachable;
#endif
      cont.push_back(branch);
      branch = backup;
      return res;
    };

#define pool pools.back()

    // Iota
    auto iota = [this, closing, depth](Position pos, Expr const* e) {
      // Try unify and close branch (no need to check for other closures...)
      // TODO: try optimise candidate selection...
      vector<Subs> unifiers;
      for (auto& [q, _]: branch.hashset[invert(pos)]) {
        auto unifier = Procs::unify({std::make_pair(e, q)}, pool);
        if (unifier.has_value()) {
          if (!Procs::equalAfterSubs(e, q, unifier.value())) unreachable;
          // If there's a unifier that doesn't affect other branches, we use that one and discard the rest.
          if (cont.empty() || subsStartsFrom(unifier.value(), cont.back().numUniversal)) {
            vector<Branch> backup = cont;
            pools.emplace_back();
            applySubs(unifier.value(), true);
#ifdef CHECK_INVARIANTS
            vector<Branch> t = cont;
#endif
            bool res = closing(depth);
#ifdef CHECK_INVARIANTS
            if (cont != t) unreachable;
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
        for (Subs const& unifier: unifiers) {
          pools.emplace_back();
          applySubs(unifier, false);
#ifdef CHECK_INVARIANTS
          vector<Branch> t = cont;
#endif
          bool res = closing(depth);
#ifdef CHECK_INVARIANTS
          if (cont != t) unreachable;
#endif
          cont = backup;
          pools.pop_back();
          if (res) return true;
        }
      }
      return dfs(depth);
    };

    // Unary
    auto unary = [this, closing, depth](Position pos, Expr const* e) {
      bool closed = false;
      WithCedent g(this, e, pos, &closed);
      return closed ? closing(depth) : dfs(depth);
    };

    // Alpha
    auto alpha = [this, closing, depth](Position pos1, Expr const* e1, Position pos2, Expr const* e2) {
      bool closed = false;
      WithCedent g1(this, e1, pos1, &closed);
      WithCedent g2(this, e2, pos2, &closed);
      return closed ? closing(depth) : dfs(depth);
    };

    // Beta
    auto beta = [this, closing, depth](Position pos1, Expr const* e1, Position pos2, Expr const* e2) {
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
      WithValue gd(&branch.depth, closed ? branch.depth : (branch.depth + 1));
      bool res = closed ? closing(depth) : dfs(depth + 1);
      if (inserted) cont.pop_back();
#ifdef CHECK_INVARIANTS
      if (cont != t) unreachable;
#endif
      return res;
    };

    using enum FOLForm::Tag;
    using enum Expr::VarTag;

    // Gamma
    auto gamma = [this, closing, depth](Position pos, Expr const* e, bool reentrant) {
      // TODO: selection in reentrant gamma expansions
      bool closed = false;
      size_t id = branch.numUniversal;
      Expr const* body = e->app.r->lam.r->makeReplace(pool.emplace(VMeta, id), pool);
      WithValue gn(&branch.numUniversal, branch.numUniversal + 1);
      WithCedent g(this, body, pos, &closed);

      // If `e` contains undetermined variables, it must be a result of some previous application of γ-rule.
      // In this case, the original template is already re-added, so we may avoid re-adding `e` again.
      // (TODO: try delay this to instantiation time?)
      if (e->isGround()) {                           // TODO: fix "forall, exists, forall"
        WithCedent gre(this, e, pos, &closed, true); // Re-add
        WithValue gd(&branch.depth, closed ? branch.depth : reentrant ? (branch.depth + 1) : branch.depth);
        return closed ? closing(depth) : dfs(reentrant ? (depth + 1) : depth);
      } else {
        if (reentrant) unreachable;
        return closed ? closing(depth) : dfs(depth);
      }
    };

    // Delta
    auto delta = [this, closing, depth](Position pos, Expr const* e) {
      bool closed = false;
      size_t id = numSkolem + ctx.size();
      vector<uint64_t> metas;
      for (uint64_t i = 0; i < branch.numUniversal; i++) metas.push_back(i);
      Expr const* body = e->app.r->lam.r->makeReplace(Procs::makeSkolem(id, metas, pool), pool);
      WithValue gn(&numSkolem, numSkolem + 1);
      WithCedent g(this, body, pos, &closed);
      return closed ? closing(depth) : dfs(depth);
    };

    constexpr static unsigned int order[] = {Iota, Alpha, Delta, Gamma};

    for (unsigned int i: order) {
      auto &ante = branch.cedents[i][L], &succ = branch.cedents[i][R];
      size_t &antei = branch.indices[i][L], &succi = branch.indices[i][R];

      // Left logical rules (try breaking down one antecedent)
      if (antei < ante.size()) {
        Expr const* e = ante[antei];
        WithValue gi(&antei, antei + 1);
        if (!(classify(L, e) == i || (classify(L, e) == Gamma && i == GammaRe))) unreachable;
        auto fof = FOLForm::fromExpr(e);
        switch (fof.tag) {
          case Other: return iota(L, e);
          case Equals: return iota(L, e);
          case True: return dfs(depth);
          case False: return closing(depth);
          case Not: return unary(R, fof.unary.e);
          case And: return alpha(L, fof.binary.l, L, fof.binary.r);
          case Or: unreachable;
          case Implies: unreachable;
          case Iff: {
            auto const [mp, mpr] = fof.splitIff(pool);
            return alpha(L, mp, L, mpr);
          }
          case Forall: return gamma(L, e, false);
          case Exists: return delta(L, e);
          case Unique: {
            auto const [exi, no2] = fof.splitUnique(pool);
            return alpha(L, exi, L, no2);
          }
        }
        unreachable;
      }

      // Right logical rules (try breaking down one succedent)
      if (succi < succ.size()) {
        Expr const* e = succ[succi];
        WithValue gi(&succi, succi + 1);
        if (!(classify(R, e) == i || (classify(R, e) == Gamma && i == GammaRe))) unreachable;
        auto fof = FOLForm::fromExpr(e);
        switch (fof.tag) {
          case Other: return iota(R, e);
          case Equals: return iota(R, e);
          case True: return closing(depth);
          case False: return dfs(depth);
          case Not: return unary(L, fof.unary.e);
          case And: unreachable;
          case Or: return alpha(R, fof.binary.l, R, fof.binary.r);
          case Implies: return alpha(L, fof.binary.l, R, fof.binary.r);
          case Iff: unreachable;
          case Forall: return delta(R, e);
          case Exists: return gamma(R, e, false);
          case Unique: unreachable;
        }
        unreachable;
      }
    }

    // We have used up everything except β and γre...

    // The relative order of β's does make a difference...
    // So I have to use a separate `betaUsed` mechanism...
    // TODO: sort by complexity?
    if (branch.depth < maxTabDepth) {
      unsigned int i = Beta;
      auto &ante = branch.cedents[i][L], &succ = branch.cedents[i][R];
      // size_t& antei = branch.indices[i][L], & succi = branch.indices[i][R];
      auto &anteu = branch.betaUsed[L], &succu = branch.betaUsed[R];

      for (size_t ii = 0; ii < ante.size(); ii++)
        if (!anteu[ii]) {
          Expr const* e = ante[ii];
          anteu[ii] = true;
          bool res = false;
          auto fof = FOLForm::fromExpr(e);
          switch (fof.tag) {
            case Or: res = beta(L, fof.binary.l, L, fof.binary.r); break;
            case Implies: res = beta(R, fof.binary.l, L, fof.binary.r); break;
            default: unreachable;
          }
          anteu[ii] = false;
          if (res) return true;
        }
      for (size_t ii = 0; ii < succ.size(); ii++)
        if (!succu[ii]) {
          Expr const* e = succ[ii];
          // Ahhhhhhh this is too messy
          succu[ii] = true;
          bool res = false;
          auto fof = FOLForm::fromExpr(e);
          switch (fof.tag) {
            case And: res = beta(R, fof.binary.l, R, fof.binary.r); break;
            case Iff: {
              auto const [mp, mpr] = fof.splitIff(pool);
              res = beta(R, mp, R, mpr);
            } break;
            case Unique: {
              auto const [exi, no2] = fof.splitUnique(pool);
              res = beta(R, exi, R, no2);
            } break;
            default: unreachable;
          }
          succu[ii] = false;
          if (res) return true;
        }
    }

    // The relative order of γ's are unimportant, so we could proceed with the insertion order
    if (branch.depth < maxTabDepth) {
      unsigned int i = GammaRe;
      auto &ante = branch.cedents[i][L], &succ = branch.cedents[i][R];
      size_t &antei = branch.indices[i][L], &succi = branch.indices[i][R];
      for (size_t ii = antei; ii < ante.size(); ii++) {
        Expr const* e = ante[ii];
        WithValue gi(&antei, ii + 1);
        auto fof = FOLForm::fromExpr(e);
        switch (fof.tag) {
          case Forall:
            if (gamma(L, e, true)) return true;
            break;
          default: unreachable;
        }
      }
      for (size_t ii = succi; ii < succ.size(); ii++) {
        Expr const* e = succ[ii];
        WithValue gi(&succi, ii + 1);
        auto fof = FOLForm::fromExpr(e);
        switch (fof.tag) {
          case Exists:
            if (gamma(R, e, true)) return true;
            break;
          default: unreachable;
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
    for (unsigned int i = 0; i < N; i++)
      for (Expr const* e: branch.cedents[i][L]) res += "| " + FOLForm::fromExpr(e).toString(ctx) + "\n";
    for (unsigned int i = 0; i < N; i++)
      for (Expr const* e: branch.cedents[i][R]) res += "| ⊢ " + FOLForm::fromExpr(e).toString(ctx) + "\n";
    res += "+------------------------------------\n";
    return res;
  }

  string Tableau::printStateDebug() {
    string res;
    res += "+------------------------------------\n";
    for (unsigned int i = 0; i < N; i++) {
      res += "| (" + typeToString(i) + ") " + std::to_string(branch.indices[i][L]) + "\n";
      for (Expr const* e: branch.cedents[i][L]) res += "| " + FOLForm::fromExpr(e).toString(ctx) + "\n";
    }
    for (unsigned int i = 0; i < N; i++) {
      res += "| (" + typeToString(i) + ") " + std::to_string(branch.indices[i][R]) + "\n";
      for (Expr const* e: branch.cedents[i][R]) res += "| ⊢ " + FOLForm::fromExpr(e).toString(ctx) + "\n";
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

  void Tableau::checkBranch(Branch const& b) {
    unordered_set<ExprHash, ExprHash::GetHash> ths[2] = {b.hashset[0], b.hashset[1]};
    for (unsigned int i = 0; i < N; i++) {
      for (unsigned int pos = 0; pos < 2; pos++) {
        for (Expr const* e: b.cedents[i][pos]) {
          if (!ths[pos].contains(ExprHash(e))) {
            std::cout << "Assertion failed: inconsistent state, formula" << std::endl;
            std::cout << "    " << e->toString(ctx) << std::endl;
            std::cout << "not found in hashset." << std::endl;
            unreachable;
          }
        }
      }
    }
    for (unsigned int i = 0; i < N; i++) {
      for (unsigned int pos = 0; pos < 2; pos++) {
        for (Expr const* e: b.cedents[i][pos]) { ths[pos].erase(ExprHash(e)); }
      }
    }
    for (ExprHash const& eh: ths[0]) {
      std::cout << "Assertion failed: inconsistent state, formula" << std::endl;
      std::cout << "    " << eh.e->toString(ctx) << std::endl;
      std::cout << "not found in cedents." << std::endl;
      unreachable;
    }
    for (ExprHash const& eh: ths[1]) {
      std::cout << "Assertion failed: inconsistent state, formula" << std::endl;
      std::cout << "    " << eh.e->toString(ctx) << std::endl;
      std::cout << "not found in cedents." << std::endl;
      unreachable;
    }
  }

  void Tableau::check() {
#ifdef CHECK_INVARIANTS
    checkBranch(branch);
    for (size_t ind = 0; ind < cont.size(); ind++) {
      Branch const& branch = cont[ind];
      checkBranch(branch);
      if (branch.cedents[β][L].size() != branch.betaUsed[L].size()) unreachable;
      if (branch.cedents[β][R].size() != branch.betaUsed[R].size()) unreachable;
      for (unsigned int i = 0; i < N; i++) {
        if (branch.cedents[i][L].size() != branch.timestamps[i][L].size()) unreachable;
        if (branch.cedents[i][L].size() != branch.numUniversals[i][L].size()) unreachable;
        for (Expr const* e: branch.cedents[i][L]) {
          if (e->numMeta() > branch.numUniversal) {
            std::cout << "Assertion failed at alt branch " << std::to_string(ind) << ":" << std::endl;
            std::cout << "Branch has numUniversal = " << branch.numUniversal << std::endl;
            std::cout << "But formula in L (" << typeToString(i) << ") has more:" << std::endl;
            std::cout << "    " << e->toString(ctx) << std::endl;
            debughtml("crash");
            unreachable;
          }
        }
        if (branch.cedents[i][R].size() != branch.timestamps[i][R].size()) unreachable;
        if (branch.cedents[i][R].size() != branch.numUniversals[i][R].size()) unreachable;
        for (Expr const* e: branch.cedents[i][R]) {
          if (e->numMeta() > branch.numUniversal) {
            std::cout << "Assertion failed at alt branch " << std::to_string(ind) << ":" << std::endl;
            std::cout << "Branch has numUniversal = " << branch.numUniversal << std::endl;
            std::cout << "But formula in R (" << typeToString(i) << ") has more:" << std::endl;
            std::cout << "    " << e->toString(ctx) << std::endl;
            debughtml("crash");
            unreachable;
          }
        }
      }
    }
#endif
  }

  void Tableau::debughtml(string const& filename) {
    using std::endl;
    std::ofstream out(filename + ".html");

    out << "<head><style>"
           "  table td, table td * { vertical-align: top; }"
           "  .disabled { color: #bbbbbb; }"
           "</style></head><body>";
    out << "<h1>Debug info</h1>";
    out << "<p>Number of branches: " << cont.size() + 1 << "</p>";
    out << "<p>Number of Skolem vars: " << numSkolem << "</p>";
    out << "<p>Maximum search depth: " << maxDepth << "</p>";
    out << "<p>Maximum beta-depth: " << maxTabDepth << "</p>";

    out << "<table><tbody><tr>";
    auto printBranch = [this, &out](Branch const& b, string const& name) {
      struct Item {
        size_t timestamp;
        unsigned int pos, type;
        bool active;
        size_t numUniversal;
        Expr const* e;
        auto operator<=>(Item const&) const = default;
      };

      out << "<td style=\"border: 1px solid black; padding: 10px; width: 480px;\">";
      out << "<h2>Branch " << name << ":</h2>";
      out << "<p>Number of cedents: " << b.numCedents << "</p>";
      out << "<p>Branch beta-depth: " << b.depth << "</p>";
      out << "<p>Number of universals: " << b.numUniversal << "</p>";

      vector<Item> a;
      for (unsigned int i = 0; i < N; i++) {
        for (size_t j = 0; j < b.cedents[i][L].size(); j++) {
          bool active = (i == Beta ? !b.betaUsed[L][j] : j >= b.indices[i][L]);
          a.push_back(Item{b.timestamps[i][L][j], L, i, active, b.numUniversals[i][L][j], b.cedents[i][L][j]});
        }
        for (size_t j = 0; j < b.cedents[i][R].size(); j++) {
          bool active = (i == Beta ? !b.betaUsed[R][j] : j >= b.indices[i][R]);
          a.push_back(Item{b.timestamps[i][R][j], R, i, active, b.numUniversals[i][R][j], b.cedents[i][R][j]});
        }
      }
      sort(a.begin(), a.end());

      out << "<p><b>Antecedents and succedents:</b></p>";
      for (auto& [ts, pos, type, active, numUniversal, e]: a) {
        out << "<p " << (active ? "" : "class=\"disabled\"") << ">";
        out << "<code>" << (pos == L ? "L" : "R") << " (" << typeToString(type) << ") ";
        out << FOLForm::fromExpr(e).toString(ctx) << "</code>";
        out << "<br /><sup>" << ts << "/" << numUniversal << "</sup>";
        out << "</p>";
      }
      out << "</td>";
    };
    printBranch(branch, "main");
    for (size_t i = 0; i < cont.size(); i++) { printBranch(cont[cont.size() - 1 - i], std::to_string(i)); }
    out << "</tr></tbody></table></body>" << endl;
  }

}
