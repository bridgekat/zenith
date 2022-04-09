#include <initializer_list>
#include "context.hpp"
#include "expr.hpp"


namespace Core {

  using std::string;
  using std::vector;


  #define pool pools.back()
  #define assert(expr) if (!(expr)) throw Core::Unreachable()

  Context::Context(): pools(1), entries(), indices() {
    #define var       Expr::make(pool, Expr::TVar)
    #define prop      Expr::make(pool, Expr::TProp)
    #define fun(l, r) Expr::make(pool, Expr::TFun, l, r)

    assert(Initial == addDefinition("initial", var));
    assert(Equals  == addDefinition("equals",  fun(var, fun(var, prop))));
    assert(True    == addDefinition("true",    prop));
    assert(False   == addDefinition("false",   prop));
    assert(Not     == addDefinition("not",     fun(prop, prop)));
    assert(And     == addDefinition("and",     fun(prop, fun(prop, prop))));
    assert(Or      == addDefinition("or",      fun(prop, fun(prop, prop))));
    assert(Implies == addDefinition("implies", fun(prop, fun(prop, prop))));
    assert(Iff     == addDefinition("iff",     fun(prop, fun(prop, prop))));
    assert(Forall  == addDefinition("forall",  fun(fun(var, prop), prop)));
    assert(Exists  == addDefinition("exists",  fun(fun(var, prop), prop)));
    assert(Unique  == addDefinition("unique",  fun(fun(var, prop), prop)));

    #undef var
    #undef prop
    #undef fun
  }

  size_t Context::addDefinition(const string& s, const Expr* e) {
    e->checkType(*this, pool); // TODO: make a temporary pool
    entries.emplace_back(s, e);
    return entries.size() - 1;
  }

  size_t Context::pushAssumption(const string& s, const Expr* e) {
    e->checkType(*this, pool); // TODO: make a temporary pool
    pools.emplace_back();
    entries.emplace_back(s, e);
    indices.push_back(entries.size() - 1);
    return entries.size() - 1;
  }

  // Context-changing rules (implies-intro, forall-intro) here
  bool Context::pop() {
    using enum Expr::Tag;
    using enum Expr::TypeTag;
    using enum Expr::VarTag;

    if (pools.empty() || indices.empty()) return false;
    const size_t index = indices.back(); indices.pop_back();
    const auto [s, x] = entries[index];

    #define expr(...) Expr::make(pool, __VA_ARGS__)

    // TODO: more flexible index remapping
    auto modify = [this, index] (unsigned int n, const Expr* x) {
      if (x->var.tag == VFree && x->var.id == index) return expr(VBound, n);
      if (x->var.tag == VFree && x->var.id > index) return expr(expr(VFree, x->var.id - 1), expr(VBound, n));
      return x->clone(pool);
    };

    for (size_t i = index; i + 1 < entries.size(); i++) {
      const auto [t, y] = entries[i + 1];
      if (x->tag == Type) {
        if (y->tag == Type) {
          // (X: kind, Y: kind)
          // If   Γ ∪ {s: X} ⊢ t: Y
          // Then Γ          ⊢ t: (X → Y)
          entries[i] = { t, expr(TFun, x->clone(pool), y->updateVars(0, pool, modify)) };
        } else {
          // (X: kind, Y: prop)
          // If   Γ ∪ {s: X} ⊢ t: Y
          // Then Γ          ⊢ t: (∀ s: X, Y)
          entries[i] = { t, expr(expr(VFree, Forall), expr(s, x->clone(pool), y->updateVars(0, pool, modify))) };
        }
      } else {
        if (y->tag == Type) {
          // (X: prop, Y: kind)
          // If   Γ ∪ {s: X} ⊢ t: Y
          // Then Γ          ⊢ t: Y
          entries[i] = { t, y->updateVars(0, pool, modify) };
        } else {
          // (X: prop, Y: prop)
          // If   Γ ∪ {s: X} ⊢ t: Y
          // Then Γ          ⊢ t: (X → Y)
          entries[i] = { t, expr(expr(expr(VFree, Implies), x->clone(pool)), y->updateVars(0, pool, modify)) };
        }
      }
    }
    entries.pop_back();

    #undef expr

    // Should not throw, for debugging only
    for (size_t i = index; i < entries.size(); i++) entries[i].expr->checkType(*this, pool);
    return true;
  }

  #undef assert
  #undef pool

}
