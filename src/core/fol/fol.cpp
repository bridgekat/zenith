#include "fol.hpp"


namespace Core {

  #pragma GCC diagnostic push
  #pragma GCC diagnostic ignored "-Wterminate"

  FOLContext::FOLContext(): Context() {
    #define assert(expr)  if (!(expr)) throw Unreachable()
    #define prop          Expr::make(pools.back(), Expr::SProp)
    #define type          Expr::make(pools.back(), Expr::SType)
    #define setvar        Expr::make(pools.back(), Expr::VFree, SetVar)
    #define pi(s, t, r)   Expr::make(pools.back(), Expr::PPi, s, t, r)

    assert(SetVar    == addVariable   ("setvar",    type));
    assert(Arbitrary == pushAssumption("arbitrary", setvar));
    assert(Equals    == pushAssumption("equals",    pi("x", setvar, pi("y", setvar, prop))));
    assert(True      == pushAssumption("true",      prop));
    assert(False     == pushAssumption("false",     prop));
    assert(Not       == pushAssumption("not",       pi("P", prop, prop)));
    assert(And       == pushAssumption("and",       pi("P", prop, pi("Q", prop, prop))));
    assert(Or        == pushAssumption("or",        pi("P", prop, pi("Q", prop, prop))));
    assert(Implies   == pushAssumption("implies",   pi("P", prop, pi("Q", prop, prop))));
    assert(Iff       == pushAssumption("iff",       pi("P", prop, pi("Q", prop, prop))));
    assert(Forall    == pushAssumption("forall",    pi("P", pi("x", setvar, prop), prop)));
    assert(Exists    == pushAssumption("exists",    pi("P", pi("x", setvar, prop), prop)));
    assert(Unique    == pushAssumption("unique",    pi("P", pi("x", setvar, prop), prop)));

    #undef assert
    #undef prop
    #undef type
    #undef setvar
    #undef pi
  }

  FOLForm FOLForm::fromExpr(const Expr* e) noexcept {
    using Constant = FOLContext::Constant;
    using enum Expr::Tag;
    using enum Expr::VarTag;
    switch (e->tag) {
      case Sort: return FOLForm(Other);
      case Var: {
        if (e->var.tag == VFree) {
          if (e->var.id == Constant::True) return FOLForm(True);
          if (e->var.id == Constant::False) return FOLForm(False);
        }
        return FOLForm(Other);
      }
      case App: {
        if (e->app.l->tag == Var) {
          if (e->app.l->var.tag == VFree) {
            if (e->app.l->var.id == Constant::Not) return FOLForm(Not, e->app.r);
            if (e->app.r->tag == Lam) {
              if (e->app.l->var.id == Constant::Forall) return FOLForm(Forall, e->app.r->lam.s, e->app.r->lam.r);
              if (e->app.l->var.id == Constant::Exists) return FOLForm(Exists, e->app.r->lam.s, e->app.r->lam.r);
              if (e->app.l->var.id == Constant::Unique) return FOLForm(Unique, e->app.r->lam.s, e->app.r->lam.r);
            }
          }
        } else if (e->app.l->tag == App && e->app.l->app.l->tag == Var) {
          if (e->app.l->app.l->var.tag == VFree) {
            if (e->app.l->app.l->var.id == Constant::And)     return FOLForm(And,     e->app.l->app.r, e->app.r);
            if (e->app.l->app.l->var.id == Constant::Or)      return FOLForm(Or,      e->app.l->app.r, e->app.r);
            if (e->app.l->app.l->var.id == Constant::Implies) return FOLForm(Implies, e->app.l->app.r, e->app.r);
            if (e->app.l->app.l->var.id == Constant::Iff)     return FOLForm(Iff,     e->app.l->app.r, e->app.r);
          }
        }
        return FOLForm(Other);
      }
      case Lam: return FOLForm(Other);
      case Pi: return FOLForm(Other);
    }
    throw NonExhaustive();
  }

  const Expr* FOLForm::toExpr(Allocator<Expr>& pool) const {
    using Constant = FOLContext::Constant;
    using enum Expr::VarTag;
    using enum Expr::LamTag;
    #define expr(...) Expr::make(pool, __VA_ARGS__)
    switch (tag) {
      case True:    return expr(VFree, Constant::True);
      case False:   return expr(VFree, Constant::False);
      case Not:     return expr(expr(VFree, Constant::Not), unary.l);
      case And:     return expr(expr(expr(VFree, Constant::And),     binary.l), binary.r);
      case Or:      return expr(expr(expr(VFree, Constant::Or),      binary.l), binary.r);
      case Implies: return expr(expr(expr(VFree, Constant::Implies), binary.l), binary.r);
      case Iff:     return expr(expr(expr(VFree, Constant::Iff),     binary.l), binary.r);
      case Forall:  return expr(expr(VFree, Constant::Forall), expr(LLam, s, expr(VFree, Constant::SetVar), binder.r));
      case Exists:  return expr(expr(VFree, Constant::Exists), expr(LLam, s, expr(VFree, Constant::SetVar), binder.r));
      case Unique:  return expr(expr(VFree, Constant::Unique), expr(LLam, s, expr(VFree, Constant::SetVar), binder.r));
      case Other:   throw Unreachable();
    }
    #undef expr
    throw NonExhaustive();
  }

  #pragma GCC diagnostic pop

}
