#include "environment.hpp"


namespace Eval {

  using std::string;
  using std::variant;
  using std::get, std::holds_alternative, std::visit;
  using Core::Allocator;

  // A shorter name for holds_alternative
  template <typename T, typename... Ts>
  constexpr bool holds(const variant<Ts...>& v) noexcept { return holds_alternative<T, Ts...>(v); }

  // Initialize with built-in forms and procedures
  Environment::Environment(): pool(), forms(), procs(), vars() {
    // BEGIN FLATBREAD CODE (开始摊大饼)

    procs["+"] = [] (const SExpr* e, Environment&, Core::Allocator<SExpr>& pool) -> SExpr* {
      Number res = 0;
      while (holds<Cons>(e->v)) {
        const auto& [head, tail] = get<Cons>(e->v);
        if (!holds<Number>(head->v)) throw EvalError("number expected", head);
        res += get<Number>(head->v);
        e = tail;
      }
      if (!holds<Nil>(e->v)) throw EvalError("list expected", e);
      return pool.emplaceBack(res);
    };

    procs["display"] = [] (const SExpr* e, Environment&, Core::Allocator<SExpr>& pool) -> SExpr* {
      if (holds<Cons>(e->v)) {
        const auto& [head, tail] = get<Cons>(e->v);
        if (!holds<String>(head->v)) throw EvalError("string expected", head);
        return pool.emplaceBack(get<String>(head->v));
      }
      if (!holds<Nil>(e->v)) throw EvalError("list expected", e);
      return pool.emplaceBack(Undefined{});
    };

    // ...

    // END OF FLATBREAD CODE (摊大饼结束)
  }

  SExpr* Environment::evalAll(const SExpr* e) {
    // TODO: temporary pool?
    if (holds<Nil>(e->v)) return pool.emplaceBack(Nil{});
    else if (holds<Cons>(e->v)) {
      const auto& [head, tail] = get<Cons>(e->v);
      return pool.emplaceBack(eval(head), evalAll(tail));
    }
    throw EvalError("list expected", e);
  }

  SExpr* Environment::eval(const SExpr* e) {
    // TODO: temporary pool?
    return visit(Matcher{
      [&] (Nil)               { return pool.emplaceBack(Nil{}); },
      [&] (Cons const& cons)  {
        SExpr* ehead = eval(cons.head);
        if (holds<Symbol>(ehead->v)) {
          string name = get<Symbol>(ehead->v).s;
          auto it1 = forms.find(name);
          if (it1 != forms.end()) return it1->second(cons.tail, *this, pool);
          auto it2 = procs.find(name);
          if (it2 != procs.end()) return it2->second(evalAll(cons.tail), *this, pool);
          throw EvalError("unknown symbol \"" + name + "\"", cons.head);
        }
        throw EvalError("head element " + ehead->toString() + " is not a symbol, list cannot be evaluated", cons.head);
      },
      [&] (Symbol const& sym) { return pool.emplaceBack(sym); },
      [&] (Number const& num) { return pool.emplaceBack(num); },
      [&] (String const& str) { return pool.emplaceBack(str); },
      [&] (Boolean boolean)   { return pool.emplaceBack(boolean); },
      [&] (Undefined)         { return pool.emplaceBack(Undefined{}); }
    }, e->v);
  }

}
