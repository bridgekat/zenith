#include "elab.hpp"

namespace Elab {

  using std::vector;
  using std::string;
  using std::pair;
  using namespace Core;

  using enum Expr::Tag;
  using enum Expr::SortTag;
  using enum Expr::VarTag;
  using enum Expr::LamTag;
  using enum Expr::PiTag;

  // clang-format off
  /*
  pair<const Expr*, const Expr*> inferHoles(const Expr* e, const Context& ctx, Allocator<Expr>& pool, vector<const Expr*>& stk, vector<string>& names) {
    switch (e->tag) {
      case Sort: {
        switch (e->sort.tag) {
          case SProp: return { e, pool.emplaceBack(SType) };
          case SType: return { e, pool.emplaceBack(SKind) };
          case SKind: throw InvalidExpr("\"Kind\" does not have a type", ctx, e);
        } unreachable;
      }
      case Var: {
        switch (e->var.tag) {
          case VBound:
            if (e->var.id < stk.size()) return stk[stk.size() - 1 - e->var.id]->reduce(pool);
            else throw InvalidExpr("de Bruijn index overflow", ctx, e);
          case VFree:
            if (e->var.id < ctx.size()) return ctx[e->var.id]->reduce(pool);
            else throw InvalidExpr("free variable not in context", ctx, e);
          case VMeta:
            // #####
            // Make a new metavariable `?t` as type, add has-type constraint `e stk: t`, return `?t`
        } unreachable;
      }
      case App: { // Π-elimination
        const auto tl = inferHoles(e->app.l, ctx, pool, stk, names);
        const auto tr = inferHoles(e->app.r, ctx, pool, stk, names);
        // #####
        // Add unification constraint `tl ?= Pi: tr, ?m` and return `?m`
        // if (tl->tag != Pi) throw InvalidExpr("expected function, term has type " + tl->toString(ctx, names), ctx, e->app.l);
        // if (*tl->pi.t != *tr) throw InvalidExpr("argument type mismatch, expected " + tl->pi.t->toString(ctx, names) + ", got " + tr->toString(ctx, names), ctx, e->app.r);
        // return tl->pi.r->makeReplace(e->app.r, pool)->reduce(pool);
      }
      case Lam: { // Π-introduction
        const auto tt = inferHoles(e->lam.t, ctx, pool, stk, names);
        names.push_back(e->lam.s);
        stk.push_back(e->lam.t);
        const auto tr = inferHoles(e->lam.r, ctx, pool, stk, names);
        names.pop_back();
        stk.pop_back();
        return pool.emplaceBack(PPi, e->lam.s, e->lam.t->reduce(pool), tr);
      }
      case Pi: { // Π-formation
        const auto tt = inferHoles(e->pi.t, ctx, pool, stk, names);
        names.push_back(e->pi.s);
        stk.push_back(e->pi.t);
        const auto tr = inferHoles(e->pi.r, ctx, pool, stk, names);
        names.pop_back();
        stk.pop_back();
        return pool.emplaceBack(Expr::imax(st, sr));
      }
    } unreachable;
  }
  */

}
