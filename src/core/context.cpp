#include <initializer_list>
#include "context.hpp"
#include "expr.hpp"


namespace Core {

  string showType(const Type& t) {
    string res = "";
    for (size_t i = 0; i < t.size(); i++) {
      string curr = "";
      for (int j = 0; j < t[i].first; j++) curr += "Var -> ";
      curr += (t[i].second == SVAR ? "Var" : "Prop");
      if (i + 1 < t.size()) curr = "(" + curr + ") -> ";
      res += curr;
    }
    return res;
  }

  // Context-changing rules (implies-intro, forall[func, pred]-intro) here
  bool Context::pop(Allocator<Expr>& pool) {
    using enum Expr::Tag;
    using enum Expr::VarTag;

    if (ind.empty()) return false;
    size_t index = ind.back(); ind.pop_back();
    auto entry = a[index];

    // Some helper functions and macros
    auto concat = [] (Type a, const Type& b) {
      for (auto x: b) a.push_back(x);
      return a;
    };

    #define node2(l_, tag_, r_)   Expr::make(pool, tag_, l_, r_)
    #define nodebinder(tag_, name_, r_) \
                                  Expr::make(pool, tag_, name_, 0, SVAR, r_) // This binds term variables only
    #define nodebinderks(tag_, name_, k_, s_, r_) \
                                  Expr::make(pool, tag_, name_, k_, s_, r_)
    #define nodevar(f_, id_, ...) Expr::make(pool, f_, id_, std::initializer_list<Expr*>{__VA_ARGS__})
    #define isexpr(info)          holds_alternative<const Expr*>(info)
    #define istype(info)          holds_alternative<Type>(info)
    #define expr(info)            get<const Expr*>(info)
    #define type(info)            get<Type>(info)

    // Which kind of assumption?
    if (isexpr(entry.info)) {
      const Expr* hyp = expr(entry.info);

      for (size_t i = index; i + 1 < a.size(); i++) {
        // Copy a[i + 1] to a[i], with necessary modifications...
        if (isexpr(a[i + 1].info)) {
          // Implies-intro for theorems
          auto modify = [index, &pool] (unsigned int, Expr* x) {
            // If defined after the hypothesis...
            if (x->var.vartag == FREE && x->var.id > index) x->var.id--;
            return x;
          };
          a[i] = {
            a[i + 1].name,
            node2(hyp->clone(pool), IMPLIES, expr(a[i + 1].info)->updateVars(0, pool, modify))
          };
        } else if (istype(a[i + 1].info)) {
          // No change for definitions
          a[i] = a[i + 1];
        } else throw NotImplemented();
      }
      a.pop_back();

    } else if (istype(entry.info)) {
      const Type& t = type(entry.info);
      // Assumed variable must be first- or second-order
      if (t.size() != 1) throw NotImplemented();

      for (size_t i = index; i + 1 < a.size(); i++) {
        // Copy a[i + 1] to a[i], with necessary modifications...
        if (isexpr(a[i + 1].info)) {
          // Forallfunc/pred-intro for theorems
          auto modify = [index, &pool] (unsigned int n, Expr* x) {
            // If it is the assumed variable...
            if (x->var.vartag == FREE && x->var.id == index) {
              x->var.vartag = BOUND; x->var.id = n;
            }
            // If defined after the assumed variable...
            else if (x->var.vartag == FREE && x->var.id > index) {
              x->var.id--;
              Expr* arg = nodevar(BOUND, n);
              arg->s = x->var.c; x->var.c = arg;
            }
            return x;
          };
          const Expr* ei = expr(a[i + 1].info);
          a[i] = {
            a[i + 1].name,
            (t == TTerm && ei->tag != FORALL2) ?
              nodebinder(FORALL, entry.name, ei->updateVars(0, pool, modify)) :
              nodebinderks(FORALL2, entry.name, t[0].first, t[0].second, ei->updateVars(0, pool, modify))
          };
        } else if (istype(a[i + 1].info)) {
          // Add abstraction for definitions
          const Type& ti = type(a[i + 1].info);
          a[i] = {
            a[i + 1].name,
            (t == TTerm && ti.size() == 1) ?
              Type{{ ti[0].first + 1, ti[0].second }} :
              concat(t, ti)
          };
        } else throw NotImplemented();
      }
      a.pop_back();

    } else throw NotImplemented();

    #undef node2
    #undef nodebinder
    #undef nodebinderks
    #undef nodevar
    #undef isexpr
    #undef istype
    #undef expr
    #undef type
    return true;
  }

}
