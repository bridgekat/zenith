#include "fol.hpp"
#include <type_traits>

namespace Core {

  using std::string;
  using std::vector;
  using std::pair;

  FOLContext::FOLContext():
    Context() {
#define prop        pools.back().emplace(Expr::SProp)
#define type        pools.back().emplace(Expr::SType)
#define setvar      pools.back().emplace(Expr::VFree, SetVar)
#define pi(s, t, r) pools.back().emplace(Expr::PPi, s, t, r)

    assert_always(SetVar == addDefinition("setvar", type));
    assert_always(Arbitrary == pushAssumption("arbitrary", setvar));
    assert_always(Equals == pushAssumption("equals", pi("x", setvar, pi("y", setvar, prop))));
    assert_always(True == pushAssumption("true", prop));
    assert_always(False == pushAssumption("false", prop));
    assert_always(Not == pushAssumption("not", pi("P", prop, prop)));
    assert_always(And == pushAssumption("and", pi("P", prop, pi("Q", prop, prop))));
    assert_always(Or == pushAssumption("or", pi("P", prop, pi("Q", prop, prop))));
    assert_always(Implies == pushAssumption("implies", pi("P", prop, pi("Q", prop, prop))));
    assert_always(Iff == pushAssumption("iff", pi("P", prop, pi("Q", prop, prop))));
    assert_always(Forall == pushAssumption("forall", pi("P", pi("x", setvar, prop), prop)));
    assert_always(Exists == pushAssumption("exists", pi("P", pi("x", setvar, prop), prop)));
    assert_always(Unique == pushAssumption("unique", pi("P", pi("x", setvar, prop), prop)));

#undef prop
#undef type
#undef setvar
#undef pi
  }

  FOLForm FOLForm::fromExpr(Expr const* e) noexcept {
    using Constant = FOLContext::Constant;
    using enum Expr::Tag;
    using enum Expr::VarTag;
    if (e->tag == Var) {
      if (e->var.tag == VFree) {
        if (e->var.id == Constant::True) return {True};
        if (e->var.id == Constant::False) return {False};
      }
    } else if (e->tag == App) {
      auto const [l, r] = e->app;
      if (l->tag == Var) {
        if (l->var.tag == VFree) {
          if (l->var.id == Constant::Not) return {Not, r};
          if (r->tag == Lam && *r->lam.t == Expr(VFree, Constant::SetVar)) {
            if (l->var.id == Constant::Forall) return {Forall, r->lam.s, r->lam.r};
            if (l->var.id == Constant::Exists) return {Exists, r->lam.s, r->lam.r};
            if (l->var.id == Constant::Unique) return {Unique, r->lam.s, r->lam.r};
          }
        }
      } else if (l->tag == App) {
        auto const [ll, lr] = l->app;
        if (ll->tag == Var) {
          if (ll->var.tag == VFree) {
            if (ll->var.id == Constant::Equals) return {Equals, lr, r};
            if (ll->var.id == Constant::And) return {And, lr, r};
            if (ll->var.id == Constant::Or) return {Or, lr, r};
            if (ll->var.id == Constant::Implies) return {Implies, lr, r};
            if (ll->var.id == Constant::Iff) return {Iff, lr, r};
          }
        }
      }
    }
    return {Other, e};
  }

#define expr(...) pool.emplace(__VA_ARGS__)

  Expr const* FOLForm::toExpr(Allocator<Expr>& pool) const {
    using Constant = FOLContext::Constant;
    using enum Expr::VarTag;
    using enum Expr::LamTag;
    switch (tag) {
      case Other: return unary.e;
      case Equals: return expr(expr(expr(VFree, Constant::Equals), binary.l), binary.r);
      case True: return expr(VFree, Constant::True);
      case False: return expr(VFree, Constant::False);
      case Not: return expr(expr(VFree, Constant::Not), unary.e);
      case And: return expr(expr(expr(VFree, Constant::And), binary.l), binary.r);
      case Or: return expr(expr(expr(VFree, Constant::Or), binary.l), binary.r);
      case Implies: return expr(expr(expr(VFree, Constant::Implies), binary.l), binary.r);
      case Iff: return expr(expr(expr(VFree, Constant::Iff), binary.l), binary.r);
      case Forall: return expr(expr(VFree, Constant::Forall), expr(LLam, s, expr(VFree, Constant::SetVar), binder.r));
      case Exists: return expr(expr(VFree, Constant::Exists), expr(LLam, s, expr(VFree, Constant::SetVar), binder.r));
      case Unique: return expr(expr(VFree, Constant::Unique), expr(LLam, s, expr(VFree, Constant::SetVar), binder.r));
    }
    unreachable;
  }

  pair<Expr const*, Expr const*> FOLForm::splitIff(Allocator<Expr>& pool) const {
    using Constant = FOLContext::Constant;
    using enum Expr::VarTag;
    if (tag != Iff) unreachable;
    return {
      expr(expr(expr(VFree, Constant::Implies), binary.l), binary.r),
      expr(expr(expr(VFree, Constant::Implies), binary.r), binary.l),
    };
  }

  // Splits "unique x, P" into "exists x, P" and "forall x, P implies (forall y, P implies x = y)"
  // Pre (checked): `tag` is `Unique`
  pair<Expr const*, Expr const*> FOLForm::splitUnique(Allocator<Expr>& pool) const {
    using Constant = FOLContext::Constant;
    using enum Expr::VarTag;
    using enum Expr::LamTag;
    if (tag != Unique) unreachable;
    auto const setvar = expr(VFree, Constant::SetVar);
    auto const implies = expr(VFree, Constant::Implies);
    auto const forall = expr(VFree, Constant::Forall);
    auto const exists = expr(VFree, Constant::Exists);
    // clang-format off
    return {
      expr(exists, expr(LLam, s, setvar, binder.r)),
      expr(forall, expr(LLam, s, setvar,
        expr(expr(implies, binder.r),
          expr(forall, expr(LLam, s, setvar,
            expr(expr(implies, binder.r),
              expr(expr(expr(VFree, Constant::Equals), expr(VBound, 1)), expr(VBound, 0)))))))),
    };
    // clang-format on
  }

#define invprec(tag_) static_cast<std::underlying_type_t<Tag>>(tag_)

  string FOLForm::toString(Context const& ctx, vector<string>& stk) const {
    switch (tag) {
      case Other: {
        auto fe = (unary.e->tag != Expr::Sort && unary.e->tag != Expr::Var && unary.e->tag != Expr::App);
        return (fe ? "(" : "") + unary.e->toString(ctx, stk) + (fe ? ")" : "");
      }
      case Equals: return binary.l->toString(ctx, stk) + " = " + binary.r->toString(ctx, stk);
      case True: return "true";
      case False: return "false";
      case Not: {
        auto ee = FOLForm::fromExpr(unary.e);
        bool fe = (invprec(ee.tag) > invprec(tag));
        return string("~") + (fe ? "(" : "") + ee.toString(ctx, stk) + (fe ? ")" : "");
      }
      case And: {
        auto ll = FOLForm::fromExpr(binary.l), rr = FOLForm::fromExpr(binary.r);
        bool fl = (invprec(ll.tag) > invprec(tag)), fr = (invprec(rr.tag) >= invprec(tag));
        return (fl ? "(" : "") + FOLForm::fromExpr(binary.l).toString(ctx, stk) + (fl ? ")" : "") + " /\\ "
             + (fr ? "(" : "") + FOLForm::fromExpr(binary.r).toString(ctx, stk) + (fr ? ")" : "");
      }
      case Or: {
        auto ll = FOLForm::fromExpr(binary.l), rr = FOLForm::fromExpr(binary.r);
        bool fl = (invprec(ll.tag) > invprec(tag)), fr = (invprec(rr.tag) >= invprec(tag));
        return (fl ? "(" : "") + FOLForm::fromExpr(binary.l).toString(ctx, stk) + (fl ? ")" : "") + " \\/ "
             + (fr ? "(" : "") + FOLForm::fromExpr(binary.r).toString(ctx, stk) + (fr ? ")" : "");
      }
      case Implies: {
        auto ll = FOLForm::fromExpr(binary.l), rr = FOLForm::fromExpr(binary.r);
        bool fl = (invprec(ll.tag) >= invprec(tag)), fr = (invprec(rr.tag) > invprec(tag));
        return (fl ? "(" : "") + FOLForm::fromExpr(binary.l).toString(ctx, stk) + (fl ? ")" : "") + " -> "
             + (fr ? "(" : "") + FOLForm::fromExpr(binary.r).toString(ctx, stk) + (fr ? ")" : "");
      }
      case Iff: {
        auto ll = FOLForm::fromExpr(binary.l), rr = FOLForm::fromExpr(binary.r);
        bool fl = (invprec(ll.tag) >= invprec(tag)), fr = (invprec(rr.tag) >= invprec(tag));
        return (fl ? "(" : "") + FOLForm::fromExpr(binary.l).toString(ctx, stk) + (fl ? ")" : "") + " <-> "
             + (fr ? "(" : "") + FOLForm::fromExpr(binary.r).toString(ctx, stk) + (fr ? ")" : "");
      }
      case Forall: {
        string name = (s.empty() ? Expr::newName(stk.size()) : s), res = "forall " + name + ", ";
        stk.push_back(name);
        res += FOLForm::fromExpr(binder.r).toString(ctx, stk);
        stk.pop_back();
        return res;
      }
      case Exists: {
        string name = (s.empty() ? Expr::newName(stk.size()) : s), res = "exists " + name + ", ";
        stk.push_back(name);
        res += FOLForm::fromExpr(binder.r).toString(ctx, stk);
        stk.pop_back();
        return res;
      }
      case Unique: {
        string name = (s.empty() ? Expr::newName(stk.size()) : s), res = "unique " + name + ", ";
        stk.push_back(name);
        res += FOLForm::fromExpr(binder.r).toString(ctx, stk);
        stk.pop_back();
        return res;
      }
    }
    unreachable;
  }

#undef invprec
#undef expr

}
