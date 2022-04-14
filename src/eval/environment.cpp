#include "environment.hpp"
#include <vector>
#include <tuple>


namespace Eval {

  using std::string;
  using std::vector;
  using std::pair;
  using std::tuple;
  using Core::Allocator;


  // A shortcut for `std::holds_alternative<T>(e->v)`
  template <typename T>
  bool holds(const SExpr* e) noexcept { return std::holds_alternative<T>(e->v); }

  // A shortcut for `std::get<T>(e->v)` (terminates on failure)
  template <typename T>
  const T& get(const SExpr* e) noexcept { return std::get<T>(e->v); }

  // Convenient pattern-matching functions (throw customized exceptions on failure)
  template <typename T>
  const T& expect(const SExpr*) { throw Core::Unreachable(); }
  #define declareExpect(T, msg) \
    template <> \
    const T& expect<T>(const SExpr* e) { \
      try { return std::get<T>(e->v); } \
      catch (std::bad_variant_access&) { throw EvalError((msg ", got ") + e->toString(), e); } \
    }
  declareExpect(Nil,     "expected end-of-list")
  declareExpect(Cons,    "expected non-empty list")
  declareExpect(Symbol,  "expected symbol (identifier)")
  declareExpect(Number,  "expected number")
  declareExpect(String,  "expected string")
  declareExpect(Boolean, "expected boolean")
  declareExpect(Closure, "expected function")
  #undef declareExpect

  template <typename T>
  const T& getNext(const SExpr*& e) {
    const auto [head, tail] = expect<Cons>(e);
    e = tail;
    return expect<T>(head);
  }

  template <typename... Ts>
  tuple<Ts...> expectTuple(const SExpr* e) {
    // Brace-init-lists guarantee evaluation order: https://en.cppreference.com/w/cpp/language/parameter_pack
    return { getNext<Ts>(e)... };
  }

  // Match an SExpr against another SExpr (pattern)
  // (No "quotation mode" currently)
  bool match(const SExpr* e, const SExpr* pat, vector<pair<string, const SExpr*>>& bindings) {
    return std::visit(Matcher{
      [&] (Nil)               { return *e == *pat; },
      [&] (Cons const& cons)  { return holds<Cons>(e) &&
                                       match(get<Cons>(e).head, cons.head, bindings) &&
                                       match(get<Cons>(e).tail, cons.tail, bindings); },
      [&] (Symbol const& sym) { bindings.emplace_back(sym.s, e); return true; },
      [&] (Number const&)     { return *e == *pat; },
      [&] (String const&)     { return *e == *pat; },
      [&] (Boolean)           { return *e == *pat; },
      [&] (Undefined)         { return *e == *pat; },
      [&] (Closure const&)    { return *e == *pat; }
    }, pat->v);
  }

  // Initialize with built-in forms and procedures
  // See: https://github.com/digama0/mm0/blob/master/mm0-hs/mm1.md#syntax-forms
  // See: https://github.com/digama0/mm0/blob/master/mm0-hs/mm1.md#builtin-functions
  Environment::Environment(): pool(), forms(), procs(), globalEnv(pool.emplaceBack(Nil{})) {
    // BEGIN FLATBREAD CODE (开始摊大饼)

    // ===============
    // Primitive forms
    // ===============

    forms["quote"] = [&] (const SExpr* env, const SExpr* e) -> Result { return evalUnquote(env, expect<Cons>(e).head); };
    forms["unquote"] = [&] (const SExpr* env, const SExpr* e) -> Result { return eval(env, expect<Cons>(e).head); };
    forms["let"] = forms["let*"] = [&] (const SExpr* env, const SExpr* e) -> Result {
      const auto [list, t] = expect<Cons>(e);
      for (auto it = list; holds<Cons>(it); it = get<Cons>(it).tail) {
        const auto [sym, t1] = expect<Cons>(get<Cons>(it).head);
        const auto [val, t2] = expect<Cons>(t1);
        env = extend(env, expect<Symbol>(sym).s, eval(env, val), pool);
      }
      return { env, execListTailcall(env, t) };
    };
    forms["def"] = forms["define"] = [&] (const SExpr* env, const SExpr* e) -> Result {
      const auto [sym, t1] = expect<Cons>(e);
      const auto [val, t2] = expect<Cons>(t1);
      if (holds<Cons>(t2)) { // Function definition
        const auto formal = val;
        const auto es = t2;
        globalEnv = extend(globalEnv, expect<Symbol>(sym).s, pool.emplaceBack(Closure(env, formal, es)), pool);
      } else { // General definition
        globalEnv = extend(globalEnv, expect<Symbol>(sym).s, eval(env, val), pool);
      }
      return pool.emplaceBack(Undefined());
    };
    forms["set!"] = [&] (const SExpr* env, const SExpr* e) -> Result {
      const auto [sym, t1] = expect<Cons>(e);
      const auto [exp, t2] = expect<Cons>(t1);
      const auto val = eval(env, exp);
      string s = expect<Symbol>(sym).s;
      for (auto it = env; holds<Cons>(it); it = get<Cons>(it).tail) {
        auto& [lhs, rhs] = get<Cons>(get<Cons>(it).head);
        if (s == get<Symbol>(lhs).s) {
          rhs = val;
          return pool.emplaceBack(Undefined());
        }
      }
      throw EvalError("unbound symbol \"" + s + "\"", sym);
    };
    forms["fn"] = forms["lambda"] = [&] (const SExpr* env, const SExpr* e) -> Result {
      const auto [formal, es] = expect<Cons>(e);
      return pool.emplaceBack(Closure(env, formal, es));
    };
    forms["if"] = [&] (const SExpr* env, const SExpr* e) -> Result {
      const auto [test, t1] = expect<Cons>(e);
      const auto [iftrue, t2] = expect<Cons>(t1);
      const auto iffalse = (holds<Cons>(t2)? get<Cons>(t2).head : pool.emplaceBack(Undefined()));
      bool result = expect<Boolean>(eval(env, test));
      return { env, result? iftrue : iffalse };
    };

    // ====================
    // Primitive procedures
    // ====================

    procs["+"] = [&] (const SExpr*, const SExpr* e) -> Result {
      Number res = 0;
      for (auto it = e; holds<Cons>(it); it = get<Cons>(it).tail) res += expect<Number>(get<Cons>(it).head);
      return pool.emplaceBack(res);
    };
    procs["-"] = [&] (const SExpr*, const SExpr* e) -> Result {
      auto [head, tail] = expect<Cons>(e); e = tail;
      Number res = expect<Number>(head);
      if (!holds<Cons>(e)) return pool.emplaceBack(-res);
      for (auto it = e; holds<Cons>(it); it = get<Cons>(it).tail) res -= expect<Number>(get<Cons>(it).head);
      return pool.emplaceBack(res);
    };
    procs["*"] = [&] (const SExpr*, const SExpr* e) -> Result {
      Number res = 1;
      for (auto it = e; holds<Cons>(it); it = get<Cons>(it).tail) res *= expect<Number>(get<Cons>(it).head);
      return pool.emplaceBack(res);
    };
    procs["//"] = [&] (const SExpr*, const SExpr* e) -> Result {
      auto [head, tail] = expect<Cons>(e); e = tail;
      Number res = expect<Number>(head);
      for (auto it = e; holds<Cons>(it); it = get<Cons>(it).tail) res /= expect<Number>(get<Cons>(it).head);
      return pool.emplaceBack(res);
    };

    #define declareBinary(sym, op) \
      procs[sym] = [&] (const SExpr*, const SExpr* e) -> Result { \
        auto [prev, tail] = expect<Cons>(e); e = tail; \
        for (auto it = e; holds<Cons>(it); it = get<Cons>(it).tail) { \
          auto curr = get<Cons>(it).head; \
          if (!(expect<Number>(prev) op expect<Number>(curr))) return pool.emplaceBack(false); \
          prev = curr; \
        } \
        return pool.emplaceBack(true); \
      };
    declareBinary("<", <);
    declareBinary(">", <);
    declareBinary("<=", <=);
    declareBinary(">=", >=);
    declareBinary("=", ==);
    #undef declareBinary

    procs["display"] = [&] (const SExpr*, const SExpr* e) -> Result {
      const auto [head, tail] = expect<Cons>(e);
      String res = expect<String>(head);
      return pool.emplaceBack(res);
    };

    // ...

    // END OF FLATBREAD CODE (摊大饼结束)
  }

  // Environment entries are stored as pairs (improper lists)!
  const SExpr* Environment::extend(const SExpr* env, const std::string& sym, const SExpr* e, Allocator<SExpr>& pool) {
    return pool.emplaceBack(pool.emplaceBack(pool.emplaceBack(Symbol{ sym }), e), env);
  }

  const SExpr* Environment::find(const SExpr* env, const std::string& sym) {
    for (auto it = env; holds<Cons>(it); it = get<Cons>(it).tail) {
      const auto [lhs, rhs] = get<Cons>(get<Cons>(it).head);
      if (sym == get<Symbol>(lhs).s)
        return (*rhs == SExpr(Undefined()))? nullptr : rhs;
    }
    return nullptr;
  }

  const SExpr* Environment::eval(const SExpr* env, const SExpr* e) {
    restart:
    /*
    for (auto i = env; holds<Cons>(i); i = get<Cons>(i).tail) {
      auto [lhs, rhs] = get<Cons>(get<Cons>(i).head);
      std::cout << lhs->toString() << " = " << rhs->toString() << std::endl;
    }
    std::cout << std::endl;
    */
    if (holds<Symbol>(e)) {
      string sym = get<Symbol>(e).s;
      auto it = find(env, sym);
      if (it) return it;
      auto it1 = forms.find(sym);
      if (it1 != forms.end()) return e;
      auto it2 = procs.find(sym);
      if (it2 != procs.end()) return e;
      throw EvalError("unbound symbol \"" + sym + "\"", e);
    } else if (holds<Cons>(e)) {
      const auto [head, tail] = get<Cons>(e);
      const SExpr* ehead = eval(env, head);
      if (holds<Symbol>(ehead)) { // Primitive function application
        string sym = get<Symbol>(ehead).s;
        auto it1 = forms.find(sym);
        if (it1 != forms.end()) {
          auto res = it1->second(env, tail);
          if (!res.env) return res.e;
          else { env = res.env; e = res.e; goto restart; }
        }
        auto it2 = procs.find(sym);
        if (it2 != procs.end()) {
          auto res = it2->second(env, evalList(env, tail));
          if (!res.env) return res.e;
          else { env = res.env; e = res.e; goto restart; }
        }
      } else if (holds<Closure>(ehead)) { // Lambda function application
        auto cl = get<Closure>(ehead);
        vector<pair<string, const SExpr*>> bindings;
        auto params = evalList(env, tail);
        bool matched = match(params, cl.formal, bindings);
        if (!matched) throw EvalError("pattern matching failed: " + cl.formal->toString() + " ?= " + params->toString(), tail);
        env = cl.env;
        for (auto& binding: bindings) env = extend(env, binding.first, binding.second, pool);
        e = execListTailcall(env, cl.es); // Execute multiple expressions (except the last one)
        goto restart;
      }
      throw EvalError("head element " + head->toString() + " (evaluates to " + ehead->toString() + ") is not a function", head);
    } else {
      return e;
    }
  }

  const SExpr* Environment::evalList(const SExpr* env, const SExpr* e) {
    if (holds<Nil>(e)) return e;
    else if (holds<Cons>(e)) {
      auto [head, tail] = get<Cons>(e);
      const SExpr* ehead = eval(env, head);
      const SExpr* etail = evalList(env, tail);
      return (ehead == head && etail == tail)? e : pool.emplaceBack(ehead, etail);
    }
    throw EvalError("expected list", e);
  }

  const SExpr* Environment::execListTailcall(const SExpr* env, const SExpr* e) {
    for (auto it = e; holds<Cons>(it); it = get<Cons>(it).tail) {
      auto [head, tail] = get<Cons>(it);
      if (!holds<Cons>(tail)) {
        expect<Nil>(tail);
        return head;
      }
      eval(env, head);
    }
    expect<Nil>(e);
    return pool.emplaceBack(Undefined());
  }

  const SExpr* Environment::evalUnquote(const SExpr* env, const SExpr* e) {
    if (holds<Cons>(e)) {
      const auto& [head, tail] = get<Cons>(e);
      if (*head == SExpr(Symbol("unquote"))) {
        if (holds<Cons>(tail)) return eval(env, get<Cons>(tail).head);
        else throw EvalError("expected list", tail);
      }
      const SExpr* ehead = evalUnquote(env, head);
      const SExpr* etail = evalUnquote(env, tail);
      return (ehead == head && etail == tail)? e : pool.emplaceBack(ehead, etail);
    }
    return e;
  }

}
