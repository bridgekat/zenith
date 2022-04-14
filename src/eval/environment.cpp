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
  bool holds(SExpr* e) noexcept { return std::holds_alternative<T>(e->v); }

  // A shortcut for `std::get<T>(e->v)` (terminates on failure)
  template <typename T>
  T& get(SExpr* e) noexcept { return std::get<T>(e->v); }

  // Convenient pattern-matching functions (throw customized exceptions on failure)
  template <typename T>
  T& expect(SExpr*) { throw Core::Unreachable(); }
  #define declareExpect(T, msg) \
    template <> \
    T& expect<T>(SExpr* e) { \
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
  T& getNext(SExpr*& e) {
    const auto [head, tail] = expect<Cons>(e);
    e = tail;
    return expect<T>(head);
  }

  template <typename... Ts>
  tuple<Ts...> expectTuple(SExpr* e) {
    // Brace-init-lists guarantee evaluation order: https://en.cppreference.com/w/cpp/language/parameter_pack
    return { getNext<Ts>(e)... };
  }

  // Match an SExpr against another SExpr (pattern)
  // (No "quotation mode" currently)
  bool match(SExpr* e, SExpr* pat, vector<pair<string, SExpr*>>& bindings) {
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
  Environment::Environment(): pool(), forms(), procs(),
      globalEnv(pool.emplaceBack(Nil())), undefined(pool.emplaceBack(Undefined())) {
    // BEGIN FLATBREAD CODE (开始摊大饼)

    // Commonly used constants
    // const auto nil    = pool.emplaceBack(Nil());
    // const auto nzero  = pool.emplaceBack(Number(0));
    // const auto sempty = pool.emplaceBack(String(""));
    const auto btrue  = pool.emplaceBack(true);
    const auto bfalse = pool.emplaceBack(false);

    // ===============
    // Primitive forms
    // ===============

    // Quasiquotation
    forms["quote"] = [this] (SExpr* env, SExpr* e) -> Result { return evalQuasiquote(env, expect<Cons>(e).head); };
    forms["unquote"] = [this] (SExpr* env, SExpr* e) -> Result { return eval(env, expect<Cons>(e).head); };
    // Currently we don't have a `let`, and this is just a synonym of `let*`...
    forms["let"] = forms["let*"] = [this] (SExpr* env, SExpr* e) -> Result {
      const auto [defs, es] = expect<Cons>(e);
      for (auto it = defs; holds<Cons>(it); it = get<Cons>(it).tail) {
        const auto [lhs, t] = expect<Cons>(get<Cons>(it).head);
        if (holds<Cons>(lhs)) {
          // Function definition
          const auto [sym, formal] = get<Cons>(lhs);
          const auto es = t;
          env = extend(env, expect<Symbol>(sym).s, pool.emplaceBack(Closure(env, formal, es)), pool);
        } else {
          // General definition (ignores more arguments)
          const auto sym = lhs;
          const auto [val, _] = expect<Cons>(t);
          env = extend(env, expect<Symbol>(sym).s, eval(env, val), pool);
        }
      }
      return { env, evalListExceptLast(env, es) };
    };
    // Currently we don't have a `letrec`, and this is just a synonym of `letrec*`...
    forms["letrec"] = forms["letrec*"] = [this] (SExpr* env, SExpr* e) -> Result {
      const auto [defs, es] = expect<Cons>(e);
      // Add #undefined (placeholder) bindings
      vector<SExpr**> refs;
      for (auto it = defs; holds<Cons>(it); it = get<Cons>(it).tail) {
        const auto [lhs, t] = expect<Cons>(get<Cons>(it).head);
        if (holds<Cons>(lhs)) {
          // Function definition
          const auto [sym, _] = get<Cons>(lhs);
          env = extend(env, expect<Symbol>(sym).s, undefined, pool);
        } else {
          // General definition (ignores more arguments)
          const auto sym = lhs;
          env = extend(env, expect<Symbol>(sym).s, undefined, pool);
        }
        refs.push_back(&get<Cons>(get<Cons>(env).head).tail);
      }
      // Sequentially evaluate and assign
      size_t i = 0;
      for (auto it = defs; holds<Cons>(it); it = get<Cons>(it).tail) {
        const auto [lhs, t] = expect<Cons>(get<Cons>(it).head);
        if (holds<Cons>(lhs)) {
          // Function definition
          const auto [_, formal] = get<Cons>(lhs);
          const auto es = t;
          *refs[i++] = pool.emplaceBack(Closure(env, formal, es));
        } else {
          // General definition (ignores more arguments)
          const auto [val, _] = expect<Cons>(t);
          *refs[i++] = eval(env, val);
        }
      }
      return { env, evalListExceptLast(env, es) };
    };
    // Global definitions will become effective only on the next statement...
    // For local definitions, use `letrec*`.
    forms["def"] = forms["define"] = [this] (SExpr* env, SExpr* e) -> Result {
      const auto [lhs, t] = expect<Cons>(e);
      if (holds<Cons>(lhs)) {
        // Function definition
        const auto [sym, formal] = get<Cons>(lhs);
        const auto es = t;
        // Add an #undefined (placeholder) binding before evaluation
        env = extend(env, expect<Symbol>(sym).s, undefined, pool);
        // Evaluate and assign
        const auto self = pool.emplaceBack(Closure(env, formal, es));
        get<Cons>(get<Cons>(env).head).tail = self;
        globalEnv = extend(globalEnv, expect<Symbol>(sym).s, self, pool);
      } else {
        // General definition (ignores more arguments)
        const auto sym = lhs;
        const auto [val, _] = expect<Cons>(t);
        globalEnv = extend(globalEnv, expect<Symbol>(sym).s, eval(env, val), pool);
      }
      return undefined;
    };
    // This modifies nodes reachable through `env` (which prevents making `SExpr*` into const pointers)
    // Ignores more arguments
    forms["set!"] = [this] (SExpr* env, SExpr* e) -> Result {
      const auto [sym, t] = expect<Cons>(e);
      const auto [exp, _] = expect<Cons>(t);
      const auto val = eval(env, exp);
      string s = expect<Symbol>(sym).s;
      for (auto it = env; holds<Cons>(it); it = get<Cons>(it).tail) {
        auto& [lhs, rhs] = get<Cons>(get<Cons>(it).head);
        if (s == get<Symbol>(lhs).s) {
          rhs = val;
          return undefined;
        }
      }
      throw EvalError("unbound symbol \"" + s + "\"", sym);
    };
    // Currently `es` are not checked for unbound symbols
    forms["fn"] = forms["lambda"] = [this] (SExpr* env, SExpr* e) -> Result {
      const auto [formal, es] = expect<Cons>(e);
      return pool.emplaceBack(Closure(env, formal, es));
    };
    // Ignores more arguments
    forms["if"] = [this] (SExpr* env, SExpr* e) -> Result {
      const auto [test, t] = expect<Cons>(e);
      const auto [iftrue, t1] = expect<Cons>(t);
      const auto iffalse = (holds<Cons>(t1)? get<Cons>(t1).head : undefined);
      bool result = expect<Boolean>(eval(env, test));
      return { env, result? iftrue : iffalse };
    };

    // ====================
    // Primitive procedures
    // ====================

    procs["+"] = [this] (SExpr*, SExpr* e) -> Result {
      Number res = 0;
      for (auto it = e; holds<Cons>(it); it = get<Cons>(it).tail) res += expect<Number>(get<Cons>(it).head);
      return pool.emplaceBack(res);
    };
    procs["-"] = [this] (SExpr*, SExpr* e) -> Result {
      const auto [head, tail] = expect<Cons>(e); e = tail;
      Number res = expect<Number>(head);
      if (!holds<Cons>(e)) return pool.emplaceBack(-res);
      for (auto it = e; holds<Cons>(it); it = get<Cons>(it).tail) res -= expect<Number>(get<Cons>(it).head);
      return pool.emplaceBack(res);
    };
    procs["*"] = [this] (SExpr*, SExpr* e) -> Result {
      Number res = 1;
      for (auto it = e; holds<Cons>(it); it = get<Cons>(it).tail) res *= expect<Number>(get<Cons>(it).head);
      return pool.emplaceBack(res);
    };
    procs["//"] = [this] (SExpr*, SExpr* e) -> Result {
      const auto [head, tail] = expect<Cons>(e); e = tail;
      Number res = expect<Number>(head);
      for (auto it = e; holds<Cons>(it); it = get<Cons>(it).tail) res /= expect<Number>(get<Cons>(it).head);
      return pool.emplaceBack(res);
    };

    #define declareBinary(sym, op) \
      procs[sym] = [=, this] (SExpr*, SExpr* e) -> Result { \
        auto [prev, tail] = expect<Cons>(e); e = tail; \
        for (auto it = e; holds<Cons>(it); it = get<Cons>(it).tail) { \
          auto curr = get<Cons>(it).head; \
          if (!(expect<Number>(prev) op expect<Number>(curr))) return bfalse; \
          prev = curr; \
        } \
        return btrue; \
      };
    declareBinary("<", <);
    declareBinary(">", <);
    declareBinary("<=", <=);
    declareBinary(">=", >=);
    declareBinary("=", ==);
    #undef declareBinary

    procs["display"] = [this] (SExpr*, SExpr* e) -> Result {
      const auto [head, tail] = expect<Cons>(e);
      String res = expect<String>(head);
      return pool.emplaceBack(res);
    };

    // ...

    // END OF FLATBREAD CODE (摊大饼结束)
  }

  // Environment entries are stored as pairs (improper lists)!
  SExpr* Environment::extend(SExpr* env, const std::string& sym, SExpr* e, Allocator<SExpr>& pool) {
    return pool.emplaceBack(pool.emplaceBack(pool.emplaceBack(Symbol{ sym }), e), env);
  }

  SExpr* Environment::find(SExpr* env, const std::string& sym) {
    for (auto it = env; holds<Cons>(it); it = get<Cons>(it).tail) {
      const auto [lhs, rhs] = get<Cons>(get<Cons>(it).head);
      if (sym == get<Symbol>(lhs).s)
        return (*rhs == SExpr(Undefined()))? nullptr : rhs;
    }
    return nullptr;
  }

  SExpr* Environment::eval(SExpr* env, SExpr* e) {
    restart:
    /*
    for (auto i = env; holds<Cons>(i); i = get<Cons>(i).tail) {
      const auto [lhs, rhs] = get<Cons>(get<Cons>(i).head);
      std::cout << lhs->toString() << " = " << rhs->toString() << std::endl;
    }
    std::cout << std::endl;
    */
    if (holds<Symbol>(e)) {
      string sym = get<Symbol>(e).s;
      const auto it = find(env, sym);
      if (it) return it;
      const auto it1 = forms.find(sym);
      if (it1 != forms.end()) return e;
      const auto it2 = procs.find(sym);
      if (it2 != procs.end()) return e;
      throw EvalError("unbound symbol \"" + sym + "\"", e);
    } else if (holds<Cons>(e)) {
      const auto [head, tail] = get<Cons>(e);
      const auto ehead = eval(env, head);
      if (holds<Symbol>(ehead)) { // Primitive function application
        string sym = get<Symbol>(ehead).s;
        const auto it1 = forms.find(sym);
        if (it1 != forms.end()) {
          const auto res = it1->second(env, tail);
          if (!res.env) return res.e;
          else { env = res.env; e = res.e; goto restart; }
        }
        const auto it2 = procs.find(sym);
        if (it2 != procs.end()) {
          const auto res = it2->second(env, evalList(env, tail));
          if (!res.env) return res.e;
          else { env = res.env; e = res.e; goto restart; }
        }
      } else if (holds<Closure>(ehead)) { // Lambda function application
        const auto cl = get<Closure>(ehead);
        vector<pair<string, SExpr*>> bindings;
        const auto params = evalList(env, tail);
        bool matched = match(params, cl.formal, bindings);
        if (!matched) throw EvalError("pattern matching failed: " + cl.formal->toString() + " ?= " + params->toString(), tail);
        env = cl.env;
        for (const auto& binding: bindings) env = extend(env, binding.first, binding.second, pool);
        e = evalListExceptLast(env, cl.es);
        goto restart;
      }
      throw EvalError("head element " + head->toString() + " (evaluates to " + ehead->toString() + ") is not a function", head);
    } else {
      return e;
    }
  }

  SExpr* Environment::evalList(SExpr* env, SExpr* e) {
    if (holds<Nil>(e)) return e;
    else if (holds<Cons>(e)) {
      const auto [head, tail] = get<Cons>(e);
      const auto ehead = eval(env, head);
      const auto etail = evalList(env, tail);
      return (ehead == head && etail == tail)? e : pool.emplaceBack(ehead, etail);
    }
    throw EvalError("expected list", e);
  }

  // Execute multiple expressions (except the last one)
  // Returns the last one, or `#undefined` if list is empty
  SExpr* Environment::evalListExceptLast(SExpr* env, SExpr* e) {
    for (auto it = e; holds<Cons>(it); it = get<Cons>(it).tail) {
      const auto [head, tail] = get<Cons>(it);
      if (!holds<Cons>(tail)) {
        expect<Nil>(tail);
        return head;
      }
      eval(env, head);
    }
    expect<Nil>(e);
    return undefined;
  }

  SExpr* Environment::evalQuasiquote(SExpr* env, SExpr* e) {
    if (holds<Cons>(e)) {
      const auto [head, tail] = get<Cons>(e);
      if (*head == SExpr(Symbol("unquote"))) {
        if (holds<Cons>(tail)) return eval(env, get<Cons>(tail).head);
        else throw EvalError("expected list", tail);
      }
      const auto ehead = evalQuasiquote(env, head);
      const auto etail = evalQuasiquote(env, tail);
      return (ehead == head && etail == tail)? e : pool.emplaceBack(ehead, etail);
    }
    return e;
  }

}
