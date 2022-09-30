#include "procs.hpp"

namespace Elab::Procs {

  bool propValue(Expr const* e, vector<bool> const& fvmap) noexcept {
    using enum FOLForm::Tag;
    auto fof = FOLForm::fromExpr(e);
    switch (fof.tag) {
      case Other:
        if (e->tag != Expr::Var || e->var.tag != Expr::VFree) unreachable;
        return (e->var.id < fvmap.size()) ? fvmap[e->var.id] : false;
      case Equals: unreachable;
      case True: return true;
      case False: return false;
      case Not: return !propValue(fof.unary.e, fvmap);
      case And: return propValue(fof.binary.l, fvmap) && propValue(fof.binary.r, fvmap);
      case Or: return propValue(fof.binary.l, fvmap) || propValue(fof.binary.r, fvmap);
      case Implies: return !propValue(fof.binary.l, fvmap) || propValue(fof.binary.r, fvmap);
      case Iff: return propValue(fof.binary.l, fvmap) == propValue(fof.binary.r, fvmap);
      case Forall: unreachable;
      case Exists: unreachable;
      case Unique: unreachable;
    }
    unreachable;
  }

  Expr const* nnf(Expr const* e, Allocator<Expr>& pool, bool f) {
    using enum FOLForm::Tag;
    auto fof = FOLForm::fromExpr(e);
    switch (fof.tag) {
      case Other: return f ? FOLForm(Not, e).toExpr(pool) : e;
      case Equals: return f ? FOLForm(Not, e).toExpr(pool) : e;
      case True: return f ? FOLForm(False).toExpr(pool) : e;
      case False: return f ? FOLForm(True).toExpr(pool) : e;
      case Not: return nnf(fof.unary.e, pool, !f);
      case And: return FOLForm(f ? Or : And, nnf(fof.binary.l, pool, f), nnf(fof.binary.r, pool, f)).toExpr(pool);
      case Or: return FOLForm(f ? And : Or, nnf(fof.binary.l, pool, f), nnf(fof.binary.r, pool, f)).toExpr(pool);
      case Implies: return FOLForm(f ? And : Or, nnf(fof.binary.l, pool, !f), nnf(fof.binary.r, pool, f)).toExpr(pool);
      case Iff: {
        auto const [mp, mpr] = fof.splitIff(pool);
        return FOLForm(f ? Or : And, nnf(mp, pool, f), nnf(mpr, pool, f)).toExpr(pool);
      }
      case Forall: return FOLForm(f ? Exists : Forall, fof.s, nnf(fof.binder.r, pool, f)).toExpr(pool);
      case Exists: return FOLForm(f ? Forall : Exists, fof.s, nnf(fof.binder.r, pool, f)).toExpr(pool);
      case Unique: {
        auto const [exi, no2] = fof.splitUnique(pool);
        return FOLForm(f ? Or : And, nnf(exi, pool, f), nnf(no2, pool, f)).toExpr(pool);
      }
    }
    unreachable;
  }

  Expr const* skolemize(
    Expr const* e, uint64_t& meta, uint64_t& skolem, vector<uint64_t>& metas, Allocator<Expr>& pool
  ) {
    using enum Expr::VarTag;
    using enum FOLForm::Tag;
    auto fof = FOLForm::fromExpr(e);
    switch (fof.tag) {
      case Other: return e;
      case Equals: return e;
      case True: return e;
      case False: return e;
      case Not: {
        auto tag = FOLForm::fromExpr(fof.unary.e).tag;
        if (tag == Other || tag == Equals) return e; // Irreducible literal
        return skolemize(nnf(e, pool), meta, skolem, metas, pool);
      }
      case And: {
        auto const l = skolemize(fof.binary.l, meta, skolem, metas, pool);
        auto const r = skolemize(fof.binary.r, meta, skolem, metas, pool);
        return (l == fof.binary.l && r == fof.binary.r) ? e : FOLForm(And, l, r).toExpr(pool);
      }
      case Or: {
        auto const l = skolemize(fof.binary.l, meta, skolem, metas, pool);
        auto const r = skolemize(fof.binary.r, meta, skolem, metas, pool);
        return (l == fof.binary.l && r == fof.binary.r) ? e : FOLForm(Or, l, r).toExpr(pool);
      }
      case Implies: return skolemize(nnf(e, pool), meta, skolem, metas, pool);
      case Iff: return skolemize(nnf(e, pool), meta, skolem, metas, pool);
      case Forall: {
        metas.push_back(meta);
        auto const ee = fof.binder.r->makeReplace(pool.emplaceBack(VMeta, meta++), pool);
        auto const res = skolemize(ee, meta, skolem, metas, pool);
        metas.pop_back();
        return res;
      }
      case Exists: {
        auto const ee = fof.binder.r->makeReplace(makeSkolem(skolem++, metas, pool), pool);
        return skolemize(ee, meta, skolem, metas, pool);
      }
      case Unique: return skolemize(nnf(e, pool), meta, skolem, metas, pool);
    }
    unreachable;
  }

  template <typename T>
  vector<T> concat(vector<T> a, vector<T> const& b) {
    for (auto const& x: b) a.push_back(x);
    return a;
  }

  template <typename T>
  vector<vector<T>> distrib(vector<vector<T>> const& a, vector<vector<T>> const& b) {
    vector<vector<T>> res;
    for (auto const& x: a)
      for (auto const& y: b) res.push_back(concat(x, y));
    return res;
  }

  // TODO: simplification of clauses
  vector<vector<Expr const*>> cnf(Expr const* e, Allocator<Expr>& pool) {
    using enum Expr::VarTag;
    using enum FOLForm::Tag;
    auto fof = FOLForm::fromExpr(e);
    switch (fof.tag) {
      case Other: return {{e}};
      case Equals: return {{e}};
      case True: return {};
      case False: return {{}};
      case Not: return {{e}}; // Not splitted
      case And: return concat(cnf(fof.binary.l, pool), cnf(fof.binary.r, pool));
      case Or: return distrib(cnf(fof.binary.l, pool), cnf(fof.binary.r, pool));
      case Implies: return {{e}}; // Not splitted
      case Iff: return {{e}};     // Not splitted
      case Forall: return {{e}};  // Not splitted
      case Exists: return {{e}};  // Not splitted
      case Unique: return {{e}};  // Not splitted
    }
    unreachable;
  }

  string showClauses(vector<vector<Expr const*>> const& cs, Context const& ctx) {
    string res = "{";
    bool f = true;
    for (auto const& c: cs) {
      res += f ? "\n  " : "\n  "; // res += f? " " : ", ";
      f = false;
      res += "{";
      bool g = true;
      for (Expr const* lit: c) {
        res += g ? " " : ", ";
        g = false;
        res += FOLForm::fromExpr(lit).toString(ctx);
      }
      res += g ? "}" : " }";
    }
    res += f ? "}" : "\n}"; // res += f? "}" : " }";
    return res;
  }

  /*
  Expr const* collectClauses(vector<vector<Expr const*>> const& cs, Allocator<Expr>& pool) {
    using enum FOLForm::Tag;
    // Construct conjunction of disjunctions
    Expr const* res = nullptr;
    for (auto const& c: cs) {
      Expr const* curr = nullptr;
      for (Expr const* lit: c) {
        curr = (curr? FOLForm(Or, curr, lit).toExpr(pool) : lit);
      }
      if (!curr) curr = FOLForm(False).toExpr(pool);
      res = (res? FOLForm(And, res, curr).toExpr(pool) : curr);
    }
    if (!res) res = FOLForm(True).toExpr(pool);
    // Add quantifiers for universals (metas)
    // uint64_t m = res->numMeta();
    // res = res->updateVars([m, &pool] (uint64_t n, Expr const* x) {
    //   return (x->var.tag == Expr::VMeta)? pool.emplaceBack(Expr::VBound, n + m - 1 - x->var.id) : x;
    // }, pool);
    // for (uint64_t i = 0; i < m; i++) res = FOLForm(Forall, "", res).toExpr(pool);
    return res;
  }
  */

  string showSubs(Subs const& subs, Context const& ctx) {
    using enum Expr::VarTag;
    string res;
    for (size_t i = 0; i < subs.size(); i++)
      if (subs[i]) { res += Expr(VMeta, i).toString(ctx) + " => " + subs[i]->toString(ctx) + "\n"; }
    return res;
  }

  bool equalAfterSubs(Expr const* lhs, Expr const* rhs, Subs const& subs) noexcept {
    using enum Expr::Tag;
    using enum Expr::VarTag;
    // Check if an undetermined variable has been replaced
    if (lhs->tag == Var && lhs->var.tag == VMeta && lhs->var.id < subs.size() && subs[lhs->var.id])
      return equalAfterSubs(subs[lhs->var.id], rhs, subs);
    if (rhs->tag == Var && rhs->var.tag == VMeta && rhs->var.id < subs.size() && subs[rhs->var.id])
      return equalAfterSubs(lhs, subs[rhs->var.id], subs);
    // Normal comparison (refer to the implementation of `Expr::operator==`)
    if (lhs->tag != rhs->tag) return false;
    switch (lhs->tag) {
      case Sort: return lhs->sort.tag == rhs->sort.tag;
      case Var: return lhs->var.tag == rhs->var.tag && lhs->var.id == rhs->var.id;
      case App: return equalAfterSubs(lhs->app.l, rhs->app.l, subs) && equalAfterSubs(lhs->app.r, rhs->app.r, subs);
      case Lam: return equalAfterSubs(lhs->lam.t, rhs->lam.t, subs) && equalAfterSubs(lhs->lam.r, rhs->lam.r, subs);
      case Pi: return equalAfterSubs(lhs->pi.t, rhs->pi.t, subs) && equalAfterSubs(lhs->pi.r, rhs->pi.r, subs);
    }
    unreachable;
  }

  // A simple anti-unification procedure. O(min(lhs size, rhs size))
  // See: https://en.wikipedia.org/wiki/Anti-unification_(computer_science)#First-order_syntactical_anti-unification
  class Antiunifier {
  public:
    Allocator<Expr>& pool;
    Subs ls, rs;

    Antiunifier(Allocator<Expr>& pool): pool(pool), ls(), rs() {}

    Expr const* dfs(Expr const* lhs, Expr const* rhs) {
      using enum Expr::Tag;
      // If roots are different, return this
      auto different = [this, lhs, rhs]() {
        uint64_t id = ls.size();
        ls.push_back(lhs);
        rs.push_back(rhs);
        return pool.emplaceBack(Expr::VMeta, id);
      };
      if (lhs->tag != rhs->tag) return different();
      // lhs->tag == rhs->tag
      switch (lhs->tag) {
        case Sort: return (lhs->sort.tag == rhs->sort.tag) ? lhs : different();
        case Var: return (lhs->var.tag == rhs->var.tag && lhs->var.id == rhs->var.id) ? lhs : different();
        case App: {
          auto const l = dfs(lhs->app.l, rhs->app.l);
          auto const r = dfs(lhs->app.r, rhs->app.r);
          return (l == lhs->app.l && r == lhs->app.r) ? lhs : pool.emplaceBack(l, r);
        }
        case Lam: {
          auto const t = dfs(lhs->lam.t, rhs->lam.t);
          auto const r = dfs(lhs->lam.r, rhs->lam.r);
          return (t == lhs->lam.t && r == lhs->lam.r) ? lhs : pool.emplaceBack(Expr::LLam, lhs->lam.s, t, r);
        }
        case Pi: {
          auto const t = dfs(lhs->pi.t, rhs->pi.t);
          auto const r = dfs(lhs->pi.r, rhs->pi.r);
          return (t == lhs->pi.t && r == lhs->pi.r) ? lhs : pool.emplaceBack(Expr::PPi, lhs->pi.s, t, r);
        }
      }
      unreachable;
    }

    tuple<Expr const*, Subs, Subs> operator()(Expr const* lhs, Expr const* rhs) {
      ls.clear();
      rs.clear();
      Expr const* c = dfs(lhs, rhs);
      return {c, ls, rs};
    }
  };

  tuple<Expr const*, Subs, Subs> antiunify(Expr const* lhs, Expr const* rhs, Allocator<Expr>& pool) {
    return Antiunifier(pool)(lhs, rhs);
  }

  // The Robinson's unification algorithm (could take exponential time for certain cases).
  // See: https://en.wikipedia.org/wiki/Unification_(computer_science)#A_unification_algorithm
  optional<Subs> unify(vector<pair<Expr const*, Expr const*>> a, Allocator<Expr>& pool) {
    using enum Expr::Tag;
    using enum Expr::VarTag;
    Subs res;

    // Add a new substitution to `res`, then update the rest of `a` to eliminate the variable with id `id`.
    auto putsubs = [&res, &pool, &a](uint64_t id, Expr const* e, size_t i0) {
      // Make enough space
      while (id >= res.size()) res.push_back(nullptr);
      // id < res.size()
      res[id] = e;
      // Update the rest of `a`
      auto f = [id, e](uint64_t, Expr const* x) { return (x->var.tag == VMeta && x->var.id == id) ? e : x; };
      for (size_t i = i0; i < a.size(); i++) {
        a[i].first = a[i].first->updateVars(f, pool);
        a[i].second = a[i].second->updateVars(f, pool);
      }
    };

    // Each step transforms `a` into an equivalent set of equations
    // (in `a` and `res`; the latter contains equations in triangular/solved form.)
    for (size_t i = 0; i < a.size(); i++) {
      Expr const *lhs = a[i].first, *rhs = a[i].second;
      if (lhs->tag == Var && lhs->var.tag == VMeta) {
        if (*lhs != *rhs) {
          // Variable elimination on the left.
          if (rhs->occurs(VMeta, lhs->var.id)) return nullopt;
          else putsubs(lhs->var.id, rhs, i + 1);
        }
      } else if (rhs->tag == Var && rhs->var.tag == VMeta) {
        if (*lhs != *rhs) {
          // Variable elimination on the right.
          if (lhs->occurs(VMeta, rhs->var.id)) return nullopt;
          else putsubs(rhs->var.id, lhs, i + 1);
        }
      } else {
        // Try term reduction.
        if (lhs->tag != rhs->tag) return nullopt;
        // lhs->tag == rhs->tag
        switch (lhs->tag) {
          case Sort:
            if (lhs->sort.tag != rhs->sort.tag) return nullopt;
            break;
          case Var:
            if (lhs->var.tag != rhs->var.tag || lhs->var.id != rhs->var.id) return nullopt;
            break;
          case App:
            a.emplace_back(lhs->app.l, rhs->app.l);
            a.emplace_back(lhs->app.r, rhs->app.r);
            break;
          case Lam:
            a.emplace_back(lhs->lam.t, rhs->lam.t);
            a.emplace_back(lhs->lam.r, rhs->lam.r);
            break;
          case Pi:
            a.emplace_back(lhs->pi.t, rhs->pi.t);
            a.emplace_back(lhs->pi.r, rhs->pi.r);
            break;
        }
      }
    }

    return res;
  }

}
