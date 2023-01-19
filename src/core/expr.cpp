#include "expr.hpp"
#include <type_traits>

namespace Core {

  using std::string;
  using std::vector;

  Expr const* Expr::clone(Allocator<Expr>& pool) const {
    switch (tag) {
      case Sort: return pool.emplace(sort.tag);
      case Var: return pool.emplace(var.tag, var.id);
      case App: return pool.emplace(app.l->clone(pool), app.r->clone(pool));
      case Lam: return pool.emplace(LLam, lam.s, lam.t->clone(pool), lam.r->clone(pool));
      case Pi: return pool.emplace(PPi, pi.s, pi.t->clone(pool), pi.r->clone(pool));
    }
    unreachable;
  }

  bool Expr::operator==(Expr const& rhs) const noexcept {
    if (this == &rhs) return true;
    if (tag != rhs.tag) return false;
    // Mid: tag == rhs.tag
    switch (tag) {
      case Sort: return sort.tag == rhs.sort.tag;
      case Var: return var.tag == rhs.var.tag && var.id == rhs.var.id;
      case App: return *app.l == *rhs.app.l && *app.r == *rhs.app.r;
      case Lam: return *lam.t == *rhs.lam.t && *lam.r == *rhs.lam.r; // Ignore bound variable names
      case Pi: return *pi.t == *rhs.pi.t && *pi.r == *rhs.pi.r;      // Ignore bound variable names
    }
    unreachable;
  }

  size_t Expr::hash() const noexcept {
    auto res = static_cast<size_t>(tag);
    switch (tag) {
      case Sort: res = hashCombine(res, static_cast<std::underlying_type_t<SortTag>>(sort.tag)); return res;
      case Var:
        res = hashCombine(res, static_cast<std::underlying_type_t<VarTag>>(var.tag));
        res = hashCombine(res, var.id);
        return res;
      case App:
        res = hashCombine(res, app.l->hash());
        res = hashCombine(res, app.r->hash());
        return res;
      case Lam:
        // Ignore bound variable names
        res = hashCombine(res, lam.t->hash());
        res = hashCombine(res, lam.r->hash());
        return res;
      case Pi:
        // Ignore bound variable names
        res = hashCombine(res, pi.t->hash());
        res = hashCombine(res, pi.r->hash());
        return res;
    }
    unreachable;
  }

  // Give unnamed bound variables a random name
  string Expr::newName(size_t i) {
    constexpr size_t Letters = 26;
    string res = "__";
    do {
      res.push_back('a' + static_cast<char>(i % Letters));
      i /= Letters;
    } while (i > 0);
    return res;
  }

  // Undefined variables should be OK, as long as pointers are valid.
  string Expr::toString(Context const& ctx, vector<string>& stk) const {
    switch (tag) {
      case Sort:
        switch (sort.tag) {
          case SProp: return "Prop";
          case SType: return "Type";
          case SKind: return "Kind";
        }
        unreachable;
      case Var:
        switch (var.tag) {
          case VBound:
            if (var.id < stk.size()) return stk[stk.size() - 1 - var.id];
            return "?b" + std::to_string(var.id - stk.size());
          case VFree:
            if (var.id < ctx.size()) return ctx.identifier(var.id);
            return "?f" + std::to_string(var.id - ctx.size());
          case VMeta: return "?m" + std::to_string(var.id);
        }
        unreachable;
      case App: {
        bool fl = (app.l->tag != Sort && app.l->tag != Var && app.l->tag != App);
        bool fr = (app.r->tag != Sort && app.r->tag != Var);
        return (fl ? "(" : "") + app.l->toString(ctx, stk) + (fl ? ")" : "") + " " + (fr ? "(" : "")
             + app.r->toString(ctx, stk) + (fr ? ")" : "");
      }
      case Lam: {
        string res, name = lam.s.empty() ? newName(stk.size()) : lam.s;
        res = "\\" + name + ": " + lam.t->toString(ctx, stk);
        stk.push_back(name);
        res += " => " + lam.r->toString(ctx, stk);
        stk.pop_back();
        return res;
      }
      case Pi: {
        string res, name = pi.s.empty() ? newName(stk.size()) : pi.s;
        res = "(" + name + ": " + pi.t->toString(ctx, stk) + ")";
        stk.push_back(name);
        res += " -> " + pi.r->toString(ctx, stk);
        stk.pop_back();
        return res;
      }
    }
    unreachable;
  }

  // Check if the subtree is a well-formed term (1), type (2), proof (3) or formula (4).
  // (1) Returns a well-formed, beta-reduced expression of type `Type`, representing the type of the term;
  // (2) Returns `Type` itself;
  // (3) Returns a well-formed, beta-reduced expression of type `Prop`, representing the proposition it proves;
  // (4) Returns `Prop` itself.
  Expr const*
  Expr::checkType(Context const& ctx, Allocator<Expr>& pool, vector<Expr const*>& stk, vector<string>& names) const {
    switch (tag) {
      case Sort:
        switch (sort.tag) {
          case SProp: return pool.emplace(SType);
          case SType: return pool.emplace(SKind);
          case SKind: throw InvalidExpr("\"Kind\" does not have a type", ctx, this);
        }
        unreachable;
      case Var:
        switch (var.tag) {
          case VBound:
            if (var.id < stk.size()) return stk[stk.size() - 1 - var.id]->lift(var.id + 1, pool)->reduce(pool);
            else throw InvalidExpr("de Bruijn index overflow", ctx, this);
          case VFree:
            if (var.id < ctx.size()) return ctx[var.id]->reduce(pool);
            else throw InvalidExpr("free variable not in context", ctx, this);
          case VMeta: throw InvalidExpr("unexpected metavariable", ctx, this);
        }
        unreachable;
      case App: { // Π-elimination
        auto const tl = app.l->checkType(ctx, pool, stk, names);
        if (tl->tag != Pi)
          throw InvalidExpr("expected function, term has type " + tl->toString(ctx, names), ctx, app.l);
        auto const tr = app.r->checkType(ctx, pool, stk, names);
        if (*tl->pi.t != *tr)
          throw InvalidExpr(
            "argument type mismatch, expected " + tl->pi.t->toString(ctx, names) + ", got " + tr->toString(ctx, names),
            ctx,
            app.r
          );
        return tl->pi.r->makeReplace(app.r, pool)->reduce(pool);
      }
      case Lam: { // Π-introduction
        auto const tt = lam.t->checkType(ctx, pool, stk, names);
        if (tt->tag != Sort)
          throw InvalidExpr("expected proposition or type, got " + tt->toString(ctx, names), ctx, lam.t);
        names.push_back(lam.s);
        stk.push_back(lam.t);
        auto const tr = lam.r->checkType(ctx, pool, stk, names);
        names.pop_back();
        stk.pop_back();
        return pool.emplace(PPi, lam.s, lam.t->reduce(pool), tr);
      }
      case Pi: { // Π-formation
        auto const tt = pi.t->checkType(ctx, pool, stk, names);
        if (tt->tag != Sort)
          throw InvalidExpr("expected proposition or type, got " + tt->toString(ctx, names), ctx, pi.t);
        names.push_back(pi.s);
        stk.push_back(pi.t);
        auto const tr = pi.r->checkType(ctx, pool, stk, names);
        if (tr->tag != Sort)
          throw InvalidExpr("expected proposition or type, got " + tr->toString(ctx, names), ctx, pi.r);
        names.pop_back();
        stk.pop_back();
        return pool.emplace(imax(tt->sort.tag, tr->sort.tag));
      }
    }
    unreachable;
  }

  Expr const* Expr::reduce(Allocator<Expr>& pool) const {
    switch (tag) {
      case Sort: return this;
      case Var: return this;
      case App: {
        // Applicative order: reduce subexpressions first
        auto const l = app.l->reduce(pool);
        auto const r = app.r->reduce(pool);
        if (l->tag == Lam) return l->lam.r->makeReplace(r, pool)->reduce(pool);
        return (l == app.l && r == app.r) ? this : pool.emplace(l, r);
      }
      case Lam: {
        auto const t = lam.t->reduce(pool);
        auto const r = lam.r->reduce(pool);
        return (t == lam.t && r == lam.r) ? this : pool.emplace(LLam, lam.s, t, r);
      }
      case Pi: {
        auto const t = pi.t->reduce(pool);
        auto const r = pi.r->reduce(pool);
        return (t == pi.t && r == pi.r) ? this : pool.emplace(PPi, pi.s, t, r);
      }
    }
    unreachable;
  }

  size_t Expr::size() const noexcept {
    switch (tag) {
      case Sort: return 1;
      case Var: return 1;
      case App: return 1 + app.l->size() + app.r->size();
      case Lam: return 1 + lam.t->size() + lam.r->size();
      case Pi: return 1 + pi.t->size() + pi.r->size();
    }
    unreachable;
  }

  bool Expr::occurs(VarTag vartag, uint64_t id) const noexcept {
    switch (tag) {
      case Sort: return false;
      case Var: return var.tag == vartag && var.id == id;
      case App: return app.l->occurs(vartag, id) || app.r->occurs(vartag, id);
      case Lam: return lam.t->occurs(vartag, id) || lam.r->occurs(vartag, id);
      case Pi: return pi.t->occurs(vartag, id) || pi.r->occurs(vartag, id);
    }
    unreachable;
  }

  size_t Expr::numMeta() const noexcept {
    switch (tag) {
      case Sort: return 0;
      case Var: return (var.tag == VMeta) ? (var.id + 1) : 0;
      case App: return std::max(app.l->numMeta(), app.r->numMeta());
      case Lam: return std::max(lam.t->numMeta(), lam.r->numMeta());
      case Pi: return std::max(pi.t->numMeta(), pi.r->numMeta());
    }
    unreachable;
  }

}
