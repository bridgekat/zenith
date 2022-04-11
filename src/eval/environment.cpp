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
  Environment::Environment(): forms(), procs(), vars() {
    // BEGIN FLATBREAD CODE (开始摊大饼)

    forms["def"] = [] (const SExpr* e, Environment& env) -> const SExpr* {
      // Not the same as MM1: no local scopes, no "begin-list"
      if (holds<Cons>(e->v)) {
        const auto& [head, tail] = get<Cons>(e->v);
        if (holds<Symbol>(head->v)) {
          string name = get<Symbol>(head->v).s;
          if (holds<Cons>(tail->v)) {
            const SExpr* val = env.eval(get<Cons>(tail->v).head);
            // env.vars[name] = val->clone(env.pool); // #####
            return temp().emplaceBack(Undefined());
          }
          else throw EvalError("expected non-empty list", tail);
        }
        else throw EvalError("expected symbol", head);
      }
      else throw EvalError("expected non-empty list", e);
    };

    forms["quote"] = [] (const SExpr* e, Environment& env) -> const SExpr* {
      if (holds<Cons>(e->v)) return env.evalUnquote(get<Cons>(e->v).head);
      else throw EvalError("expected non-empty list", e);
    };

    forms["unquote"] = [] (const SExpr* e, Environment& env) -> const SExpr* {
      if (holds<Cons>(e->v)) return env.eval(get<Cons>(e->v).head);
      else throw EvalError("expected non-empty list", e);
    };

    procs["+"] = [] (const SExpr* e, Environment&) -> const SExpr* {
      Number res = 0;
      while (holds<Cons>(e->v)) {
        const auto& [head, tail] = get<Cons>(e->v);
        if (!holds<Number>(head->v)) throw EvalError("expected number", head);
        res += get<Number>(head->v);
        e = tail;
      }
      if (!holds<Nil>(e->v)) throw EvalError("expected list", e);
      return temp().emplaceBack(res);
    };

    procs["display"] = [] (const SExpr* e, Environment&) -> const SExpr* {
      if (holds<Cons>(e->v)) {
        const auto& [head, tail] = get<Cons>(e->v);
        if (!holds<String>(head->v)) throw EvalError("expected string", head);
        return head;
      }
      else throw EvalError("expected non-empty list", e);
    };

    // ...

    // END OF FLATBREAD CODE (摊大饼结束)
  }

  const SExpr* Environment::eval(const SExpr* e) {
    return visit(Matcher{
      [&] (Nil)               { return e; },
      [&] (Cons const& cons)  {
        const SExpr* ehead = eval(cons.head);
        if (holds<Symbol>(ehead->v)) {
          string name = get<Symbol>(ehead->v).s;
          auto it1 = forms.find(name);
          if (it1 != forms.end()) {
            try { return it1->second(cons.tail, *this); }
            catch (EvalError& ex) { ex.e = e; throw ex; }
          }
          auto it2 = procs.find(name);
          if (it2 != procs.end()) {
            try { return it2->second(evalList(cons.tail), *this); }
            catch (EvalError& ex) { ex.e = e; throw ex; }
          }
          auto it3 = vars.find(name);
          if (it3 != vars.end()) {
            // #####
          }
          throw EvalError("unknown symbol \"" + name + "\"", cons.head, e);
        }
        throw EvalError("head element " + ehead->toString() + " is not a symbol", cons.head, e);
      },
      [&] (Symbol const&) { return e; },
      [&] (Number const&) { return e; },
      [&] (String const&) { return e; },
      [&] (Boolean)       { return e; },
      [&] (Undefined)     { return e; }
    }, e->v);
  }

  const SExpr* Environment::evalList(const SExpr* e) {
    if (holds<Nil>(e->v)) return e;
    else if (holds<Cons>(e->v)) {
      const auto& [head, tail] = get<Cons>(e->v);
      const SExpr* ehead = eval(head);
      const SExpr* etail = evalList(tail);
      return (ehead == head && etail == tail)? e : temp().emplaceBack(ehead, etail);
    }
    throw EvalError("expected list", e);
  }

  const SExpr* Environment::evalUnquote(const SExpr* e) {
    if (holds<Cons>(e->v)) {
      const auto& [head, tail] = get<Cons>(e->v);
      if (*head == SExpr(Symbol("unquote"))) {
        if (holds<Cons>(tail->v)) return eval(get<Cons>(tail->v).head);
        else throw EvalError("expected list", tail);
      }
      const SExpr* ehead = evalUnquote(head);
      const SExpr* etail = evalUnquote(tail);
      return (ehead == head && etail == tail)? e : temp().emplaceBack(ehead, etail);
    }
    return e;
  }

}
