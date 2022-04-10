#include "environment.hpp"


namespace Eval {

  using std::string;
  using std::get, std::holds_alternative, std::visit;
  using Core::Allocator;


  Environment::Environment(): pool(), forms(), procs(), vars() {
    procs["+"] = [] (const SExpr* e, Environment&, Core::Allocator<SExpr>& pool) -> SExpr* {
      Number res = 0;
      while (holds_alternative<Cons>(e->v)) {
        const auto& [hd, tl] = get<Cons>(e->v);
        if (!holds_alternative<Number>(hd->v)) throw EvalError("number expected", hd);
        res += get<Number>(hd->v);
        e = tl;
      }
      if (!holds_alternative<Nil>(e->v)) throw EvalError("list expected", e);
      return pool.emplaceBack(res);
    };
  }

  SExpr* Environment::evalAll(const SExpr* e) {
    if (holds_alternative<Nil>(e->v)) return pool.emplaceBack(Nil{});
    else if (holds_alternative<Cons>(e->v)) {
      const auto& [hd, tl] = get<Cons>(e->v);
      return pool.emplaceBack(eval(hd), evalAll(tl));
    }
    throw EvalError("list expected", e);
  }

  SExpr* Environment::eval(const SExpr* e) {
    // TODO: temporary pool?
    return visit(Matcher{
      [&] (Nil)               { return pool.emplaceBack(Nil{}); },
      [&] (const Cons& cons)  {
        SExpr* ehead = eval(cons.head);
        if (holds_alternative<Symbol>(ehead->v)) {
          string name = get<Symbol>(ehead->v).s;
          auto it1 = forms.find(name);
          if (it1 != forms.end()) return it1->second(cons.tail, *this, pool);
          auto it2 = procs.find(name);
          if (it2 != procs.end()) return it2->second(evalAll(cons.tail), *this, pool);
          throw EvalError("unknown symbol \"" + name + "\"", cons.head);
        }
        throw EvalError("head element " + ehead->toString() + " is not a symbol, list cannot be evaluated", cons.head);
      },
      [&] (const Symbol& sym) { return pool.emplaceBack(sym); },
      [&] (const Number& num) { return pool.emplaceBack(num); },
      [&] (const String& str) { return pool.emplaceBack(str); },
      [&] (Boolean boolean)   { return pool.emplaceBack(boolean); },
      [&] (Undefined)         { return pool.emplaceBack(Undefined{}); }
    }, e->v);
  }

}
