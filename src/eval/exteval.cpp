#include "exteval.hpp"

namespace Eval {

  using std::string;
  using std::vector;
  using std::pair;
  using std::optional;
  using Core::Expr, Core::Allocator;


  #define cons        pool.emplaceBack
  #define nil         nil
  #define sym(s)      pool.emplaceBack(Symbol{ s })
  #define str(s)      pool.emplaceBack(String{ s })
  #define nat(n)      pool.emplaceBack(Nat64{ n })
  #define boolean(b)  pool.emplaceBack(Bool{ b })
  #define obj(n)      pool.emplaceBack(Native{ n })
  #define unit        unit
  #define list(...)   makeList({ __VA_ARGS__ })

  ExtendedEvaluator::ExtendedEvaluator(): Evaluator(), ctx(), epool() {

    // =========================
    // ApiMu-specific procedures
    // =========================

    // [!] Conversions between lists and native objects (`Expr`)
    addPrimitive("tree_expr", { true, [this] (Tree*, Tree* e) -> Result {
      return obj(treeExpr(expect<Cons>(e).head));
    }});
    addPrimitive("expr_tree", { true, [this] (Tree*, Tree* e) -> Result {
      return exprTree(expectNative<const Expr*>(expect<Cons>(e).head));
    }});

    // [?] TEMP CODE
    addPrimitive("context_size", { true, [this] (Tree*, Tree*) -> Result {
      return nat(static_cast<uint64_t>(ctx.size()));
    }});
    addPrimitive("context_get", { true, [this] (Tree*, Tree* e) -> Result {
      uint64_t i = expect<Nat64>(expect<Cons>(e).head).val;
      size_t index = static_cast<size_t>(i);
      if (index < ctx.size()) return cons(str(ctx.identifier(index)), cons(obj(ctx[index]), nil));
      return unit;
    }});
    addPrimitive("context_push", { true, [this] (Tree*, Tree* e) -> Result {
      const auto& [lhs, t] = expect<Cons>(expect<Cons>(e).head);
      const auto& [rhs, _] = expect<Cons>(t);
      string s = expect<String>(lhs).val;
      const Expr* expr = expectNative<const Expr*>(rhs);
      try { ctx.pushAssumption(s, expr); return unit; }
      catch (std::runtime_error& ex) { return str(ex.what()); }
    }});
    addPrimitive("context_pop", { true, [this] (Tree*, Tree*) -> Result {
      try { ctx.pop(); return unit; }
      catch (std::runtime_error& ex) { return str(ex.what()); }
    }});
    addPrimitive("expr_print", { true, [this] (Tree*, Tree* e) -> Result {
      return str(expectNative<const Expr*>(expect<Cons>(e).head)->toString(ctx));
    }});
    addPrimitive("expr_fprint", { true, [this] (Tree*, Tree* e) -> Result {
      return str(Core::FOLForm::fromExpr(expectNative<const Expr*>(expect<Cons>(e).head)).toString(ctx));
    }});
    addPrimitive("expr_check", { true, [this] (Tree*, Tree* e) -> Result {
      try { return obj(expectNative<const Expr*>(expect<Cons>(e).head)->checkType(ctx, epool)); }
      catch (std::runtime_error& ex) { return str(ex.what()); }
    }});

    // [?] TEMP CODE
    addPrimitive("expr_make_bound", { true, [this] (Tree*, Tree* e) -> Result {
      const auto& [h, t] = expect<Cons>(e);
      const auto& [h1, u] = expect<Cons>(t);
      uint64_t id = expect<Nat64>(h1).val;
      const auto res = treeExpr(h)->makeBound(id, epool);
      return exprTree(res);
    }});
    addPrimitive("expr_make_replace", { true, [this] (Tree*, Tree* e) -> Result {
      const auto& [h, t] = expect<Cons>(e);
      const auto& [h1, u] = expect<Cons>(t);
      const auto res = treeExpr(h)->makeReplace(treeExpr(h1), epool);
      return exprTree(res);
    }});

  }

  Tree* ExtendedEvaluator::exprTree(const Expr* e) {
    using enum Expr::Tag;
    using enum Expr::SortTag;
    using enum Expr::VarTag;
    switch (e->tag) {
      case Sort:
        switch (e->sort.tag) {
          case SProp: return cons(sym("Sort"), cons(sym("Prop"), nil));
          case SType: return cons(sym("Sort"), cons(sym("Type"), nil));
          case SKind: return cons(sym("Sort"), cons(sym("Kind"), nil));
        }
        break;
      case Var:
        switch (e->var.tag) {
          case VBound: return cons(sym("Var"), cons(sym("Bound"), cons(nat(static_cast<Nat64>(e->var.id)), nil)));
          case VFree:  return cons(sym("Var"), cons(sym("Free"),  cons(nat(static_cast<Nat64>(e->var.id)), nil)));
          case VMeta:  return cons(sym("Var"), cons(sym("Meta"),  cons(nat(static_cast<Nat64>(e->var.id)), nil)));
        }
        break;
      case App: return cons(sym("App"),                     cons(exprTree(e->app.l), cons(exprTree(e->app.r), nil)));
      case Lam: return cons(sym("Lam"), cons(str(e->lam.s), cons(exprTree(e->lam.t), cons(exprTree(e->lam.r), nil))));
      case Pi:  return cons(sym("Pi"),  cons(str(e->pi.s),  cons(exprTree(e->pi.t),  cons(exprTree(e->pi.r),  nil))));
    } exhaustive;
  }

  const Expr* ExtendedEvaluator::treeExpr(Tree* e) {
    using enum Expr::Tag;
    #define expr epool.emplaceBack
    const auto& [h, t] = expect<Cons>(e);
    string sym = expect<Symbol>(h).val;
    if (sym == "Sort") {
      const auto& [h1, _] = expect<Cons>(t);
      expect<Nil>(_);
      string tag = expect<Symbol>(h1).val;
      if      (tag == "Prop") return expr(Expr::SProp);
      else if (tag == "Type") return expr(Expr::SType);
      else if (tag == "Kind") return expr(Expr::SKind);
      else throw PartialEvalError(R"(tag must be "Prop", "Type" or "Kind")", h1);
    } else if (sym == "Var") {
      const auto& [h1, u] = expect<Cons>(t);
      const auto& [h2, _] = expect<Cons>(u);
      expect<Nil>(_);
      string tag = expect<Symbol>(h1).val;
      uint64_t id = expect<Nat64>(h2).val;
      if      (tag == "Bound") return expr(Expr::VBound, static_cast<uint64_t>(id));
      else if (tag == "Free")  return expr(Expr::VFree,  static_cast<uint64_t>(id));
      else if (tag == "Meta")  return expr(Expr::VMeta,  static_cast<uint64_t>(id));
      else throw PartialEvalError(R"(tag must be "Bound", "Free" or "Meta")", h1);
    } else if (sym == "App") {
      const auto& [h1, u] = expect<Cons>(t);
      const auto& [h2, _] = expect<Cons>(u);
      expect<Nil>(_);
      return expr(treeExpr(h1), treeExpr(h2));
    } else if (sym == "Lam") {
      const auto& [h1, u] = expect<Cons>(t);
      const auto& [h2, v] = expect<Cons>(u);
      const auto& [h3, _] = expect<Cons>(v);
      expect<Nil>(_);
      return expr(Expr::LLam, expect<String>(h1).val, treeExpr(h2), treeExpr(h3));
    } else if (sym == "Pi") {
      const auto& [h1, u] = expect<Cons>(t);
      const auto& [h2, v] = expect<Cons>(u);
      const auto& [h3, _] = expect<Cons>(v);
      expect<Nil>(_);
      return expr(Expr::PPi, expect<String>(h1).val, treeExpr(h2), treeExpr(h3));
    } else throw PartialEvalError(R"(symbol must be "Sort", "Var", "App", "Lam" or "Pi")", h);
    #undef expr
  }

  #undef cons
  #undef nil
  #undef sym
  #undef str
  #undef nat
  #undef boolean
  #undef obj
  #undef unit
  #undef list

}
