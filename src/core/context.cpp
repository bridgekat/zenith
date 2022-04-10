#include <initializer_list>
#include "context.hpp"
#include "expr.hpp"


namespace Core {

  using std::string;
  using std::vector;


  #define pool pools.back()
  #define assert(expr) if (!(expr)) throw Core::Unreachable()

  Context::Context(): pools(1), entries(), indices() {
    #define prop        Expr::make(pool, Expr::SProp)
    #define type        Expr::make(pool, Expr::SType)
    #define setvar      Expr::make(pool, Expr::VFree, SetVar)
    #define pi(s, t, r) Expr::make(pool, Expr::PPi, s, t, r)

    assert(SetVar  == addDefinition("setvar",  type));
    assert(Initial == addDefinition("initial", setvar));
    assert(Equals  == addDefinition("equals",  pi("x", setvar, pi("y", setvar, prop))));
    assert(True    == addDefinition("true",    prop));
    assert(False   == addDefinition("false",   prop));
    assert(Not     == addDefinition("not",     pi("P", prop, prop)));
    assert(And     == addDefinition("and",     pi("P", prop, pi("Q", prop, prop))));
    assert(Or      == addDefinition("or",      pi("P", prop, pi("Q", prop, prop))));
    assert(Implies == addDefinition("implies", pi("P", prop, pi("Q", prop, prop))));
    assert(Iff     == addDefinition("iff",     pi("P", prop, pi("Q", prop, prop))));
    assert(Forall  == addDefinition("forall",  pi("P", pi("x", setvar, prop), prop)));
    assert(Exists  == addDefinition("exists",  pi("P", pi("x", setvar, prop), prop)));
    assert(Unique  == addDefinition("unique",  pi("P", pi("x", setvar, prop), prop)));

    #undef var
    #undef prop
    #undef fun
  }

  size_t Context::addDefinition(const string& s, const Expr* e) {
    if (*e != Expr(Expr::SType)) e->checkType(*this, pool); // TODO: make a temporary pool
    entries.emplace_back(s, e);
    return entries.size() - 1;
  }

  size_t Context::pushAssumption(const string& s, const Expr* e) {
    if (*e != Expr(Expr::SType)) e->checkType(*this, pool); // TODO: make a temporary pool
    pools.emplace_back();
    entries.emplace_back(s, e);
    indices.push_back(entries.size() - 1);
    return entries.size() - 1;
  }

  // Context-changing rules (implies/forall-intro) & definition generalization rules here
  bool Context::pop() {
    using enum Expr::Tag;
    using enum Expr::SortTag;
    using enum Expr::VarTag;
    using enum Expr::LamTag;
    using enum Expr::PiTag;

    if (pools.empty() || indices.empty()) return false;
    const size_t index = indices.back();
    const auto [s, x] = entries[index];

    #define expr(...) Expr::make(pool, __VA_ARGS__)

    /*
    // TODO: more flexible index remapping
    auto modify = [this, index] (uint64_t n, const Expr* x) {
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
    */

    #undef expr

    // Should not throw, for debugging only
    for (size_t i = index; i < entries.size(); i++) entries[i].second->checkType(*this, pool);

    indices.pop_back();
    return true;
  }

  #undef assert
  #undef pool

}
