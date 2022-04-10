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
  // See: https://github.com/digama0/mm0/blob/master/mm0-hs/mm1.md#syntax-forms
  // See: https://github.com/digama0/mm0/blob/master/mm0-hs/mm1.md#builtin-functions
  Environment::Environment(): pool(), forms(), procs(), vars() {
    // BEGIN FLATBREAD CODE (开始摊大饼)

    procs["+"] = [] (const SExpr* e, Environment&, Core::Allocator<SExpr>& pool) -> const SExpr* {
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

    procs["display"] = [] (const SExpr* e, Environment&, Core::Allocator<SExpr>& pool) -> const SExpr* {
      if (holds<Cons>(e->v)) {
        const auto& [head, tail] = get<Cons>(e->v);
        if (!holds<String>(head->v)) throw EvalError("string expected", head);
        return head;
      }
      if (!holds<Nil>(e->v)) throw EvalError("list expected", e);
      return pool.emplaceBack(Undefined{});
    };

    // ...

    // END OF FLATBREAD CODE (摊大饼结束)
  }

  const SExpr* Environment::evalAll(const SExpr* e) {
    // TODO: temporary pool?
    if (holds<Nil>(e->v)) return e;
    else if (holds<Cons>(e->v)) {
      const auto& [head, tail] = get<Cons>(e->v);
      const SExpr* ehead = eval(head);
      const SExpr* etail = evalAll(tail);
      return (ehead == head && etail == tail)? e : pool.emplaceBack(ehead, etail);
    }
    throw EvalError("list expected", e);
  }

  const SExpr* Environment::eval(const SExpr* e) {
    // TODO: temporary pool?
    return visit(Matcher{
      [&] (Nil)               { return e; },
      [&] (Cons const& cons)  {
        const SExpr* ehead = eval(cons.head);
        if (holds<Symbol>(ehead->v)) {
          string name = get<Symbol>(ehead->v).s;
          auto it1 = forms.find(name);
          if (it1 != forms.end()) {
            try {
              return it1->second(cons.tail, *this, pool);
            } catch (EvalError& ex) {
              ex.e = e;
              throw ex;
            }
          }
          auto it2 = procs.find(name);
          if (it2 != procs.end()) {
            try {
              return it2->second(evalAll(cons.tail), *this, pool);
            } catch (EvalError& ex) {
              ex.e = e;
              throw ex;
            }
          }
          throw EvalError("unknown symbol \"" + name + "\"", cons.head, e);
        }
        throw EvalError("head element " + ehead->toString() + " is not a symbol, list cannot be evaluated", cons.head, e);
      },
      [&] (Symbol const&) { return e; },
      [&] (Number const&) { return e; },
      [&] (String const&) { return e; },
      [&] (Boolean)       { return e; },
      [&] (Undefined)     { return e; }
    }, e->v);
  }

}
