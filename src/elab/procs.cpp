#include "procs.hpp"


namespace Elab::Procs {

  // Allow throwing in `noexcept` functions; we really intend to terminate with an error message
  #pragma GCC diagnostic push
  #pragma GCC diagnostic ignored "-Wterminate"

  bool propValue(const Expr* e, const vector<bool>& fvmap) noexcept {
    using enum FOLForm::Tag;
    auto fof = FOLForm::fromExpr(e);
    switch (fof.tag) {
      case True:    return true;
      case False:   return false;
      case Not:     return !propValue(fof.unary.e, fvmap);
      case And:     return  propValue(fof.binary.l, fvmap) && propValue(fof.binary.r, fvmap);
      case Or:      return  propValue(fof.binary.l, fvmap) || propValue(fof.binary.r, fvmap);
      case Implies: return !propValue(fof.binary.l, fvmap) || propValue(fof.binary.r, fvmap);
      case Iff:     return  propValue(fof.binary.l, fvmap) == propValue(fof.binary.r, fvmap);
      case Forall:  throw Unreachable();
      case Exists:  throw Unreachable();
      case Unique:  throw Unreachable();
      case Other:   if (e->tag != Expr::Var || e->var.tag != Expr::VFree) throw Unreachable();
                    return (e->var.id < fvmap.size())? fvmap[e->var.id] : false;
    }
    throw NonExhaustive();
  }

  const Expr* nnf(const Expr* e, Allocator<Expr>& pool, bool negated) {
    using enum FOLForm::Tag;
    auto fof = FOLForm::fromExpr(e);
    switch (fof.tag) {
      case True:      return FOLForm(negated? False : True).toExpr(pool);
      case False:     return FOLForm(negated? True : False).toExpr(pool);
      case Not:       return nnf(fof.unary.e, pool, !negated);
      case And:       return FOLForm(negated? Or : And, nnf(fof.binary.l, pool, negated), nnf(fof.binary.r, pool, negated)).toExpr(pool);
      case Or:        return FOLForm(negated? And : Or, nnf(fof.binary.l, pool, negated), nnf(fof.binary.r, pool, negated)).toExpr(pool);
      case Implies:   return FOLForm(negated? And : Or, nnf(fof.binary.l, pool, !negated), nnf(fof.binary.r, pool, negated)).toExpr(pool);
      case Iff:     { const auto [mp, mpr] = fof.splitIff(pool);
                      return FOLForm(negated? Or : And, nnf(mp, pool, negated), nnf(mpr, pool, negated)).toExpr(pool); }
      case Forall:    return FOLForm(negated? Exists : Forall, fof.s, nnf(fof.binder.r, pool, negated)).toExpr(pool);
      case Exists:    return FOLForm(negated? Forall : Exists, fof.s, nnf(fof.binder.r, pool, negated)).toExpr(pool);
      case Unique:  { const auto [exi, no2] = fof.splitUnique(pool);
                      return FOLForm(negated? Or : And, nnf(exi, pool, negated), nnf(no2, pool, negated)).toExpr(pool); }
      case Other:     return negated? FOLForm(Not, e).toExpr(pool) : e;
    }
    throw NonExhaustive();
  }

  template <typename T>
  vector<T> concat(vector<T> a, const vector<T>& b) {
    for (const auto& x: b) a.push_back(x);
    return a;
  }

  template <typename T>
  vector<vector<T>> distrib(const vector<vector<T>>& a, const vector<vector<T>>& b) {
    vector<vector<T>> res;
    for (const auto& x: a) for (const auto& y: b) res.push_back(concat(x, y));
    return res;
  }

  vector<vector<const Expr*>> cnf(const Expr* e, uint64_t meta, uint64_t skolem, Allocator<Expr>& pool) {
    using enum Expr::VarTag;
    using enum FOLForm::Tag;
    auto fof = FOLForm::fromExpr(e);
    switch (fof.tag) {
      case True:    return {};
      case False:   return {{}};
      case Not:     return {{ e }}; // Not splitted
      case And:     return concat(cnf(fof.binary.l, meta, skolem, pool), cnf(fof.binary.r, meta, skolem, pool));
      case Or:      return distrib(cnf(fof.binary.l, meta, skolem, pool), cnf(fof.binary.r, meta, skolem, pool));
      case Implies: return {{ e }}; // Not splitted
      case Iff:     return {{ e }}; // Not splitted
      case Forall:  return cnf(fof.binder.r->makeReplace(pool.emplaceBack(VMeta, meta), pool), meta + 1, skolem, pool);
      case Exists:  return cnf(fof.binder.r->makeReplace(makeSkolem(meta, skolem, pool), pool), meta, skolem + 1, pool);
      case Unique:  return {{ e }}; // Not splitted
      case Other:   return {{ e }}; // Not splitted
    }
    throw NonExhaustive();
  }

  string showClauses(const vector<vector<const Expr*>>& cs, const Context& ctx) {
    string res = "{";
    bool f = true;
    for (const auto& c: cs) {
      res += f? "\n  " : "\n  "; // res += f? " " : ", ";
      f = false;
      res += "{";
      bool g = true;
      for (const Expr* lit: c) {
        res += g? " " : ", ";
        g = false;
        res += FOLForm::fromExpr(lit).toString(ctx);
      }
      res += g? "}" : " }";
    }
    res += f? "}" : "\n}"; // res += f? "}" : " }";
    return res;
  }

  string showSubs(const Subs& subs, const Context& ctx) {
    using enum Expr::VarTag;
    string res;
    for (size_t i = 0; i < subs.size(); i++) if (subs[i]) {
      res += Expr(VMeta, i).toString(ctx) + " => " + subs[i]->toString(ctx) + "\n";
    }
    return res;
  }

  bool equalAfterSubs(const Expr* lhs, const Expr* rhs, const Subs& subs) noexcept {
    using enum Expr::Tag;
    using enum Expr::VarTag;
    // Check if an undetermined variable has been replaced
    if (lhs->tag == Var && lhs->var.tag == VMeta && lhs->var.id < subs.size() && subs[lhs->var.id]) return equalAfterSubs(subs[lhs->var.id], rhs, subs);
    if (rhs->tag == Var && rhs->var.tag == VMeta && rhs->var.id < subs.size() && subs[rhs->var.id]) return equalAfterSubs(lhs, subs[rhs->var.id], subs);
    // Normal comparison (refer to the implementation of `Expr::operator==`)
    if (lhs->tag != rhs->tag) return false;
    switch (lhs->tag) {
      case Sort: return lhs->sort.tag == rhs->sort.tag;
      case Var:  return lhs->var.tag == rhs->var.tag && lhs->var.id == rhs->var.id;
      case App:  return equalAfterSubs(lhs->app.l, rhs->app.l, subs) && equalAfterSubs(lhs->app.r, rhs->app.r, subs);
      case Lam:  return equalAfterSubs(lhs->lam.t, rhs->lam.t, subs) && equalAfterSubs(lhs->lam.r, rhs->lam.r, subs);
      case Pi:   return equalAfterSubs(lhs->pi.t, rhs->pi.t, subs) && equalAfterSubs(lhs->pi.r, rhs->pi.r, subs);
    }
    throw NonExhaustive();
  }

  #pragma GCC diagnostic pop

  // A simple anti-unification procedure. O(min(lhs size, rhs size))
  // See: https://en.wikipedia.org/wiki/Anti-unification_(computer_science)#First-order_syntactical_anti-unification
  class Antiunifier {
  public:
    Allocator<Expr>& pool;
    Subs ls, rs;

    Antiunifier(Allocator<Expr>& pool): pool(pool), ls(), rs() {}

    const Expr* dfs(const Expr* lhs, const Expr* rhs) {
      using enum Expr::Tag;
      // If roots are different, return this
      auto different = [this, lhs, rhs] () {
        uint64_t id = ls.size();
        ls.push_back(lhs);
        rs.push_back(rhs);
        return pool.emplaceBack(Expr::VMeta, id);
      };
      if (lhs->tag != rhs->tag) return different();
      // lhs->tag == rhs->tag
      switch (lhs->tag) {
        case Sort: return (lhs->sort.tag == rhs->sort.tag)? lhs : different();
        case Var:  return (lhs->var.tag == rhs->var.tag && lhs->var.id == rhs->var.id)? lhs : different();
        case App: {
          const auto l = dfs(lhs->app.l, rhs->app.l);
          const auto r = dfs(lhs->app.r, rhs->app.r);
          return (l == lhs->app.l && r == lhs->app.r)? lhs : pool.emplaceBack(l, r);
        }
        case Lam: {
          const auto t = dfs(lhs->lam.t, rhs->lam.t);
          const auto r = dfs(lhs->lam.r, rhs->lam.r);
          return (t == lhs->lam.t && r == lhs->lam.r)? lhs : pool.emplaceBack(Expr::LLam, lhs->lam.s, t, r);
        }
        case Pi: {
          const auto t = dfs(lhs->pi.t, rhs->pi.t);
          const auto r = dfs(lhs->pi.r, rhs->pi.r);
          return (t == lhs->pi.t && r == lhs->pi.r)? lhs : pool.emplaceBack(Expr::PPi, lhs->pi.s, t, r);
        }
      }
      throw NonExhaustive();
    }

    tuple<const Expr*, Subs, Subs> operator()(const Expr* lhs, const Expr* rhs) {
      ls.clear();
      rs.clear();
      const Expr* c = dfs(lhs, rhs);
      return { c, ls, rs };
    }
  };

  tuple<const Expr*, Subs, Subs> antiunify(const Expr* lhs, const Expr* rhs, Allocator<Expr>& pool) {
    return Antiunifier(pool)(lhs, rhs);
  }

  // The Robinson's unification algorithm (could take exponential time for certain cases).
  // See: https://en.wikipedia.org/wiki/Unification_(computer_science)#A_unification_algorithm
  optional<Subs> unify(vector<pair<const Expr*, const Expr*>> a, Allocator<Expr>& pool) {
    using enum Expr::Tag;
    using enum Expr::VarTag;
    Subs res;

    // Add a new substitution to `res`, then update the rest of `a` to eliminate the variable with id `id`.
    auto putsubs = [&res, &pool, &a] (uint64_t id, const Expr* e, size_t i0) {
      // Make enough space
      while (id >= res.size()) res.push_back(nullptr);
      // id < res.size()
      res[id] = e;
      // Update the rest of `a`
      auto f = [id, e] (uint64_t, const Expr* x) {
        return (x->var.tag == VMeta && x->var.id == id)? e : x;
      };
      for (size_t i = i0; i < a.size(); i++) {
        a[i].first = a[i].first->updateVars(f, pool);
        a[i].second = a[i].second->updateVars(f, pool);
      }
    };

    // Each step transforms `a` into an equivalent set of equations
    // (in `a` and `res`; the latter contains equations in triangular/solved form.)
    for (size_t i = 0; i < a.size(); i++) {
      const Expr* lhs = a[i].first, * rhs = a[i].second;

      if (lhs->tag == Var && lhs->var.tag == VMeta) {
        // Variable elimination on the left.
        if (*lhs == *rhs);
        else if (rhs->occurs(VMeta, lhs->var.id)) return nullopt;
        else putsubs(lhs->var.id, rhs, i + 1);

      } else if (rhs->tag == Var && rhs->var.tag == VMeta) {
        // Variable elimination on the right.
        if (*lhs == *rhs);
        else if (lhs->occurs(VMeta, rhs->var.id)) return nullopt;
        else putsubs(rhs->var.id, lhs, i + 1);

      } else {
        // Try term reduction.
        if (lhs->tag != rhs->tag) return nullopt;
        // lhs->tag == rhs->tag
        switch (lhs->tag) {
          case Sort: if (lhs->sort.tag != rhs->sort.tag) return nullopt; break;
          case Var:  if (lhs->var.tag != rhs->var.tag || lhs->var.id != rhs->var.id) return nullopt; break;
          case App:  a.emplace_back(lhs->app.l, rhs->app.l); a.emplace_back(lhs->app.r, rhs->app.r); break;
          case Lam:  a.emplace_back(lhs->lam.t, rhs->lam.t); a.emplace_back(lhs->lam.r, rhs->lam.r); break;
          case Pi:   a.emplace_back(lhs->pi.t,  rhs->pi.t);  a.emplace_back(lhs->pi.r,  rhs->pi.r);  break;
        }
      }
    }

    return res;
  }

}
