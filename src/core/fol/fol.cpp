#include "fol.hpp"
#include <type_traits>


namespace Core {

  using std::string;
  using std::vector;
  using std::pair;


  #pragma GCC diagnostic push
  #pragma GCC diagnostic ignored "-Wterminate"

  FOLContext::FOLContext(): Context() {
    #define assert(expr)  if (!(expr)) throw Unreachable()
    #define prop          Expr::make(pools.back(), Expr::SProp)
    #define type          Expr::make(pools.back(), Expr::SType)
    #define setvar        Expr::make(pools.back(), Expr::VFree, SetVar)
    #define pi(s, t, r)   Expr::make(pools.back(), Expr::PPi, s, t, r)

    assert(SetVar    == addDefinition ("setvar",    type));
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
    if (e->tag == Var) {
      if (e->var.tag == VFree) {
        if (e->var.id == Constant::True)  return FOLForm(True);  // (true)
        if (e->var.id == Constant::False) return FOLForm(False); // (false)
      }
    } else if (e->tag == App) {
      const auto [l, r] = e->app;
      if (l->tag == Var) {
        if (l->var.tag == VFree) {
          if (l->var.id == Constant::Not) return FOLForm(Not, r); // ((not) (...))
          if (r->tag == Lam && *r->lam.t == Expr(VFree, Constant::SetVar)) {
            if (l->var.id == Constant::Forall) return FOLForm(Forall, r->lam.s, r->lam.r); // ((forall) (\(x): (setvar) => (...)))
            if (l->var.id == Constant::Exists) return FOLForm(Exists, r->lam.s, r->lam.r); // ((exists) (\(x): (setvar) => (...)))
            if (l->var.id == Constant::Unique) return FOLForm(Unique, r->lam.s, r->lam.r); // ((unique) (\(x): (setvar) => (...)))
          }
        }
      } else if (l->tag == App) {
        const auto [ll, lr] = l->app;
        if (ll->tag == Var) {
          if (ll->var.tag == VFree) {
            if (ll->var.id == Constant::Equals)  return FOLForm(Equals,  lr, r); // (((equals)  (...)) (...))
            if (ll->var.id == Constant::And)     return FOLForm(And,     lr, r); // (((and)     (...)) (...))
            if (ll->var.id == Constant::Or)      return FOLForm(Or,      lr, r); // (((or)      (...)) (...))
            if (ll->var.id == Constant::Implies) return FOLForm(Implies, lr, r); // (((implies) (...)) (...))
            if (ll->var.id == Constant::Iff)     return FOLForm(Iff,     lr, r); // (((iff)     (...)) (...))
          }
        }
      }
    }
    return FOLForm(Other, e);
  }

  #define expr(...) Expr::make(pool, __VA_ARGS__)

  const Expr* FOLForm::toExpr(Allocator<Expr>& pool) const {
    using Constant = FOLContext::Constant;
    using enum Expr::VarTag;
    using enum Expr::LamTag;
    switch (tag) {
      case Other:   return unary.e;
      case Equals:  return expr(expr(expr(VFree, Constant::Equals),  binary.l), binary.r);
      case True:    return expr(VFree, Constant::True);
      case False:   return expr(VFree, Constant::False);
      case Not:     return expr(expr(VFree, Constant::Not), unary.e);
      case And:     return expr(expr(expr(VFree, Constant::And),     binary.l), binary.r);
      case Or:      return expr(expr(expr(VFree, Constant::Or),      binary.l), binary.r);
      case Implies: return expr(expr(expr(VFree, Constant::Implies), binary.l), binary.r);
      case Iff:     return expr(expr(expr(VFree, Constant::Iff),     binary.l), binary.r);
      case Forall:  return expr(expr(VFree, Constant::Forall), expr(LLam, s, expr(VFree, Constant::SetVar), binder.r));
      case Exists:  return expr(expr(VFree, Constant::Exists), expr(LLam, s, expr(VFree, Constant::SetVar), binder.r));
      case Unique:  return expr(expr(VFree, Constant::Unique), expr(LLam, s, expr(VFree, Constant::SetVar), binder.r));
    }
    throw NonExhaustive();
  }

  pair<const Expr*, const Expr*> FOLForm::splitIff(Allocator<Expr>& pool) const {
    using Constant = FOLContext::Constant;
    using enum Expr::VarTag;
    if (tag != Iff) throw Unreachable();
    return {
      expr(expr(expr(VFree, Constant::Implies), binary.l), binary.r),
      expr(expr(expr(VFree, Constant::Implies), binary.r), binary.l)
    };
  }

  // Splits "unique x, P" into "exists x, P" and "forall x, P implies (forall y, P implies x = y)"
  // Pre (checked): `tag` is `Unique`
  pair<const Expr*, const Expr*> FOLForm::splitUnique(Allocator<Expr>& pool) const {
    using Constant = FOLContext::Constant;
    using enum Expr::VarTag;
    using enum Expr::LamTag;
    if (tag != Unique) throw Unreachable();
    const auto setvar  = expr(VFree, Constant::SetVar);
    const auto implies = expr(VFree, Constant::Implies);
    const auto forall  = expr(VFree, Constant::Forall);
    const auto exists  = expr(VFree, Constant::Exists);
    return {
      expr(exists, expr(LLam, s, setvar, binder.r)),
      expr(forall, expr(LLam, s, setvar, expr(expr(implies, binder.r), 
        expr(forall, expr(LLam, s, setvar, expr(expr(implies, binder.r),
          expr(expr(expr(VFree, Constant::Equals), expr(VBound, 1)), expr(VBound, 0))))))))
    };
  }

  string FOLForm::toString(const Context& ctx, vector<string>& stk) const {
    #define invprec(tag_) static_cast<std::underlying_type_t<Tag>>(tag_)
    switch (tag) {
      case Other: {
        auto fe = (unary.e->tag != Expr::Sort && unary.e->tag != Expr::Var && unary.e->tag != Expr::App);
        return (fe? "(" : "") + unary.e->toString(ctx, stk) + (fe? ")" : "");
      }
      case Equals: return binary.l->toString(ctx, stk) + " = " + binary.r->toString(ctx, stk);
      case True:   return "true";
      case False:  return "false";
      case Not: {
        auto ee = FOLForm::fromExpr(unary.e);
        bool fe = (invprec(ee.tag) > invprec(tag));
        return string("~") + (fe? "(" : "") + ee.toString(ctx, stk) + (fe? ")" : "");
      }
      case And: {
        auto ll = FOLForm::fromExpr(binary.l), rr = FOLForm::fromExpr(binary.r);
        bool fl = (invprec(ll.tag) > invprec(tag));
        bool fr = (invprec(rr.tag) >= invprec(tag));
        return (fl? "(" : "") + FOLForm::fromExpr(binary.l).toString(ctx, stk) + (fl? ")" : "") + " /\\ " +
               (fr? "(" : "") + FOLForm::fromExpr(binary.r).toString(ctx, stk) + (fr? ")" : "");
      }
      case Or: {
        auto ll = FOLForm::fromExpr(binary.l), rr = FOLForm::fromExpr(binary.r);
        bool fl = (invprec(ll.tag) > invprec(tag));
        bool fr = (invprec(rr.tag) >= invprec(tag));
        return (fl? "(" : "") + FOLForm::fromExpr(binary.l).toString(ctx, stk) + (fl? ")" : "") + " \\/ " +
               (fr? "(" : "") + FOLForm::fromExpr(binary.r).toString(ctx, stk) + (fr? ")" : "");
      }
      case Implies: {
        auto ll = FOLForm::fromExpr(binary.l), rr = FOLForm::fromExpr(binary.r);
        bool fl = (invprec(ll.tag) >= invprec(tag));
        bool fr = (invprec(rr.tag) > invprec(tag));
        return (fl? "(" : "") + FOLForm::fromExpr(binary.l).toString(ctx, stk) + (fl? ")" : "") + " -> " +
               (fr? "(" : "") + FOLForm::fromExpr(binary.r).toString(ctx, stk) + (fr? ")" : "");
      }
      case Iff: {
        auto ll = FOLForm::fromExpr(binary.l), rr = FOLForm::fromExpr(binary.r);
        bool fl = (invprec(ll.tag) >= invprec(tag));
        bool fr = (invprec(rr.tag) >= invprec(tag));
        return (fl? "(" : "") + FOLForm::fromExpr(binary.l).toString(ctx, stk) + (fl? ")" : "") + " <-> " +
               (fr? "(" : "") + FOLForm::fromExpr(binary.r).toString(ctx, stk) + (fr? ")" : "");
      }
      case Forall: {
        string name = (s.empty()? Expr::newName(stk.size()) : s), res = "forall " + name + ", ";
        stk.push_back(name); res += FOLForm::fromExpr(binder.r).toString(ctx, stk); stk.pop_back();
        return res;
      }
      case Exists: {
        string name = (s.empty()? Expr::newName(stk.size()) : s), res = "exists " + name + ", ";
        stk.push_back(name); res += FOLForm::fromExpr(binder.r).toString(ctx, stk); stk.pop_back();
        return res;
      }
      case Unique: {
        string name = (s.empty()? Expr::newName(stk.size()) : s), res = "unique " + name + ", ";
        stk.push_back(name); res += FOLForm::fromExpr(binder.r).toString(ctx, stk); stk.pop_back();
        return res;
      }
    }
    #undef invprec
    throw NonExhaustive();
  }

  #undef expr
  #pragma GCC diagnostic pop

}
