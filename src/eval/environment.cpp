#include "environment.hpp"


namespace Eval {

  using std::string;
  using std::vector;
  using std::pair;
  using Core::Expr, Core::Allocator;


  // Throw this when you don't know about the parent expression,
  // or when you want the parent call to `eval()` to provide context.
  struct PartialEvalError: public EvalError {
    PartialEvalError(const std::string& s, const SExpr* at): EvalError(s, at, at) {}
  };

  // A shortcut for `std::holds_alternative<T>(e->v)`
  template <typename T>
  bool holds(SExpr* e) noexcept { return std::holds_alternative<T>(e->v); }

  // A shortcut for `std::get<T>(e->v)` (terminates on failure)
  template <typename T>
  T& get(SExpr* e) noexcept { return std::get<T>(e->v); }

  // Convenient pattern-matching functions (throw customized exceptions on failure)
  template <typename T>
  T& expect(SExpr*) { unreachable; }
  #define declareExpect(T, msg) \
    template <> \
    T& expect<T>(SExpr* e) { \
      try { return std::get<T>(e->v); } \
      catch (std::bad_variant_access&) { throw PartialEvalError((msg ", got ") + e->toString(), e); } \
    }
  declareExpect(Nil,     "expected end-of-list")
  declareExpect(Cons,    "expected non-empty list")
  declareExpect(Symbol,  "expected symbol")
  declareExpect(Number,  "expected number")
  declareExpect(String,  "expected string")
  declareExpect(Boolean, "expected boolean")
  declareExpect(Closure, "expected function")
  declareExpect(Native,  "expected native type")
  #undef declareExpect

  template <typename T>
  T expectNative(SExpr* e) {
    try { return std::any_cast<T>(expect<Native>(e).val); }
    catch (std::bad_any_cast& ex) { throw PartialEvalError(string("native type mismatch: ") + ex.what(), e); }
  }

  /*
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
  */

  // Match an SExpr against another SExpr (pattern)
  bool Environment::matchSimple(SExpr* e, SExpr* pat, SExpr*& env) {
    if (holds<Symbol>(pat)) {
      env = extend(env, get<Symbol>(pat).s, e);
      return true;
    }
    if (holds<Cons>(pat)) {
      auto [head, tail] = get<Cons>(pat);
      return holds<Cons>(e) &&
        matchSimple(get<Cons>(e).head, head, env) &&
        matchSimple(get<Cons>(e).tail, tail, env);
    }
    return *e == *pat;
  }

  // Match an SExpr against another SExpr (pattern)
  // See: https://github.com/digama0/mm0/blob/master/mm0-hs/mm1.md#syntax-forms
  // (Continuation, `__k`, `and`, `or`, `not` and `pred?` patterns are not implemented)
  bool Environment::matchFull(SExpr* e, SExpr* pat, SExpr*& env, bool quoteMode) {
    if (holds<Symbol>(pat) && !quoteMode) {
      string sym = get<Symbol>(pat).s;
      if (sym != "_") env = extend(env, sym, e);
      return true;
    }
    if (holds<Cons>(pat)) {
      auto [h, t] = get<Cons>(pat);
      if (holds<Symbol>(h)) {
        string sym = get<Symbol>(h).s;
        if (sym == "quote" && !quoteMode) return matchFull(e, expect<Cons>(t).head, env, true); // Enter quote mode
        if (sym == "unquote" && quoteMode) return matchFull(e, expect<Cons>(t).head, env, false); // Leave quote mode
        if (sym == "...") return holds<Nil>(e) || holds<Cons>(e);
      }
      return holds<Cons>(e) &&
        matchFull(get<Cons>(e).head, h, env, quoteMode) &&
        matchFull(get<Cons>(e).tail, t, env, quoteMode);
    }
    return *e == *pat;
  }

  // Initialize with built-in forms and procedures
  // See: https://github.com/digama0/mm0/blob/master/mm0-hs/mm1.md#syntax-forms
  // See: https://github.com/digama0/mm0/blob/master/mm0-hs/mm1.md#builtin-functions
  Environment::Environment(): pool(), epool(), ctx(), prim(), primNames(),
      globalEnv(pool.emplaceBack(Nil{})),
      nil(pool.emplaceBack(Nil{})),
      undefined(pool.emplaceBack(Undefined{})) {
    // BEGIN FLATBREAD CODE (开始摊大饼)

    // Commonly used constants
    // const auto nzero  = pool.emplaceBack(Number{ 0 });
    // const auto sempty = pool.emplaceBack(String{ "" });
    const auto btrue  = pool.emplaceBack(Boolean::True);
    const auto bfalse = pool.emplaceBack(Boolean::False);

    // ===============
    // Primitive forms
    // ===============

    // [√] Quasiquotation
    primNames["quote"] = addPrim(false, [this] (SExpr* env, SExpr* e) -> Result { return evalQuasiquote(env, expect<Cons>(e).head); });
    primNames["unquote"] = addPrim(false, [this] (SExpr* env, SExpr* e) -> Result { return eval(env, expect<Cons>(e).head); });

    // [√] Currently we don't have a `let`, and this is just a synonym of `let*`...
    primNames["let"] = primNames["let*"] = addPrim(false, [this] (SExpr* env, SExpr* e) -> Result {
      const auto [defs, es] = expect<Cons>(e);
      for (auto it = defs; holds<Cons>(it); it = get<Cons>(it).tail) {
        const auto [lhs, t] = expect<Cons>(get<Cons>(it).head);
        if (holds<Cons>(lhs)) {
          // Function definition
          const auto [sym, formal] = get<Cons>(lhs);
          const auto body = t;
          env = extend(env, expect<Symbol>(sym).s, pool.emplaceBack(Closure{ env, formal, body }));
        } else {
          // General definition (ignores more arguments)
          const auto sym = lhs;
          const auto [val, _] = expect<Cons>(t);
          env = extend(env, expect<Symbol>(sym).s, eval(env, val));
        }
      }
      return { env, evalListExceptLast(env, es) };
    });

    // [√] Currently we don't have a `letrec`, and this is just a synonym of `letrec*`...
    primNames["letrec"] = primNames["letrec*"] = addPrim(false, [this] (SExpr* env, SExpr* e) -> Result {
      const auto [defs, es] = expect<Cons>(e);
      // Add #undefined (placeholder) bindings
      vector<SExpr**> refs;
      for (auto it = defs; holds<Cons>(it); it = get<Cons>(it).tail) {
        const auto [lhs, t] = expect<Cons>(get<Cons>(it).head);
        if (holds<Cons>(lhs)) {
          // Function definition
          const auto [sym, _] = get<Cons>(lhs);
          env = extend(env, expect<Symbol>(sym).s, undefined);
        } else {
          // General definition (ignores more arguments)
          const auto sym = lhs;
          env = extend(env, expect<Symbol>(sym).s, undefined);
        }
        refs.push_back(&get<Cons>(get<Cons>(get<Cons>(env).head).tail).head); // Will always succeed due to the recent `extend`
      }
      // Sequentially evaluate and assign
      size_t i = 0;
      for (auto it = defs; holds<Cons>(it); it = get<Cons>(it).tail) {
        const auto [lhs, t] = expect<Cons>(get<Cons>(it).head);
        if (holds<Cons>(lhs)) {
          // Function definition
          const auto [_, formal] = get<Cons>(lhs);
          const auto body = t;
          *refs[i++] = pool.emplaceBack(Closure{ env, formal, body });
        } else {
          // General definition (ignores more arguments)
          const auto [val, _] = expect<Cons>(t);
          *refs[i++] = eval(env, val);
        }
      }
      return { env, evalListExceptLast(env, es) };
    });

    // [√] This modifies nodes reachable through `env` (which prevents making `SExpr*` into const pointers)
    // Ignores more arguments
    primNames["set!"] = addPrim(false, [this] (SExpr* env, SExpr* e) -> Result {
      const auto [sym, t] = expect<Cons>(e);
      const auto [exp, _] = expect<Cons>(t);
      const auto val = eval(env, exp);
      string s = expect<Symbol>(sym).s;
      for (auto it = env; holds<Cons>(it); it = get<Cons>(it).tail) {
        const auto curr = get<Cons>(it).head;
        if (holds<Cons>(curr)) {
          const auto [lhs, t1] = get<Cons>(curr);
          auto&      [rhs, t2] = get<Cons>(t1);
          if (holds<Symbol>(lhs) && get<Symbol>(lhs).s == s) { rhs = val; return undefined; }
        }
      }
      throw PartialEvalError("unbound symbol \"" + s + "\"", sym);
    });

    // [√]
    primNames["fn"] = primNames["lambda"] = addPrim(false, [this] (SExpr* env, SExpr* e) -> Result {
      const auto [formal, es] = expect<Cons>(e);
      return pool.emplaceBack(Closure{ env, formal, es });
    });

    // [√] Ignores more arguments
    primNames["if"] = addPrim(false, [this] (SExpr* env, SExpr* e) -> Result {
      const auto [test, t] = expect<Cons>(e);
      const auto [iftrue, t1] = expect<Cons>(t);
      const auto iffalse = (holds<Cons>(t1)? get<Cons>(t1).head : undefined);
      bool result = (expect<Boolean>(eval(env, test)) == Boolean::True);
      return { env, result? iftrue : iffalse };
    });

    // [√]
    primNames["match"] = addPrim(false, [this] (SExpr* env, SExpr* e) -> Result {
      const auto [head, clauses] = expect<Cons>(e);
      const auto target = eval(env, head);
      for (auto it = clauses; holds<Cons>(it); it = get<Cons>(it).tail) {
        const auto [pat, t1] = expect<Cons>(get<Cons>(it).head);
        SExpr* newEnv = env;
        if (matchFull(target, pat, newEnv)) {
          const auto [expr, _] = expect<Cons>(t1);
          return { newEnv, expr };
        }
      }
      // All failed, throw exception
      string msg = "nonexhaustive patterns: { ";
      bool first = true;
      for (auto it = clauses; holds<Cons>(it); it = get<Cons>(it).tail) {
        const auto [pat, _] = expect<Cons>(get<Cons>(it).head);
        if (!first) msg += ", ";
        first = false;
        msg += pat->toString();
      }
      msg += " } ?= " + target->toString();
      throw PartialEvalError(msg, clauses);
    });

    // [√] Global definitions will become effective only on the next statement...
    // For local definitions, use `letrec*`.
    primNames["def"] = primNames["define"] = addPrim(false, [this] (SExpr* env, SExpr* e) -> Result {
      const auto [lhs, t] = expect<Cons>(e);
      if (holds<Cons>(lhs)) {
        // Function definition
        const auto [sym, formal] = get<Cons>(lhs);
        const auto es = t;
        // Add an #undefined (placeholder) binding before evaluation
        env = extend(env, expect<Symbol>(sym).s, undefined);
        // Evaluate and assign
        const auto self = pool.emplaceBack(Closure{ env, formal, es });
        get<Cons>(get<Cons>(get<Cons>(env).head).tail).head = self; // Will always succeed due to the recent `extend`
        globalEnv = extend(globalEnv, expect<Symbol>(sym).s, self);
      } else {
        // General definition (ignores more arguments)
        const auto sym = lhs;
        const auto [val, _] = expect<Cons>(t);
        globalEnv = extend(globalEnv, expect<Symbol>(sym).s, eval(env, val));
      }
      return undefined;
    });

    // ====================
    // Primitive procedures
    // ====================

    // [√]
    primNames["eval"] = addPrim(true, [] (SExpr* env, SExpr* e) -> Result {
      auto [head, tail] = expect<Cons>(e);
      if (holds<Cons>(tail)) env = expect<Cons>(tail).head;
      return { env, head }; // Let it restart and evaluate
    });
    primNames["get-env"] = addPrim(true, [] (SExpr* env, SExpr*) -> Result { return env; });
    primNames["get-global-env"] = addPrim(true, [this] (SExpr*, SExpr*) -> Result { return globalEnv; });
    primNames["set-global-env!"] = addPrim(true, [this] (SExpr*, SExpr* e) -> Result { globalEnv = expect<Cons>(e).head; return undefined; });

    // [√]
    primNames["+"] = addPrim(true, [this] (SExpr*, SExpr* e) -> Result {
      Number res = 0;
      for (auto it = e; holds<Cons>(it); it = get<Cons>(it).tail) res += expect<Number>(get<Cons>(it).head);
      return pool.emplaceBack(res);
    });
    primNames["-"] = addPrim(true, [this] (SExpr*, SExpr* e) -> Result {
      const auto [head, tail] = expect<Cons>(e); e = tail;
      Number res = expect<Number>(head);
      if (!holds<Cons>(e)) return pool.emplaceBack(-res);
      for (auto it = e; holds<Cons>(it); it = get<Cons>(it).tail) res -= expect<Number>(get<Cons>(it).head);
      return pool.emplaceBack(res);
    });
    primNames["*"] = addPrim(true, [this] (SExpr*, SExpr* e) -> Result {
      Number res = 1;
      for (auto it = e; holds<Cons>(it); it = get<Cons>(it).tail) res *= expect<Number>(get<Cons>(it).head);
      return pool.emplaceBack(res);
    });
    primNames["/"] = addPrim(true, [this] (SExpr*, SExpr* e) -> Result {
      const auto [head, tail] = expect<Cons>(e); e = tail;
      Number res = expect<Number>(head);
      for (auto it = e; holds<Cons>(it); it = get<Cons>(it).tail) res /= expect<Number>(get<Cons>(it).head);
      return pool.emplaceBack(res);
    });
    primNames["%"] = addPrim(true, [this] (SExpr*, SExpr* e) -> Result {
      const auto [head, tail] = expect<Cons>(e); e = tail;
      Number res = expect<Number>(head);
      for (auto it = e; holds<Cons>(it); it = get<Cons>(it).tail) res %= expect<Number>(get<Cons>(it).head);
      return pool.emplaceBack(res);
    });

    // [√]
    #define declareBinary(sym, op) \
      primNames[sym] = addPrim(true, [bfalse, btrue] (SExpr*, SExpr* e) -> Result { \
        auto [prev, tail] = expect<Cons>(e); e = tail; \
        for (auto it = e; holds<Cons>(it); it = get<Cons>(it).tail) { \
          auto curr = get<Cons>(it).head; \
          if (!(expect<Number>(prev) op expect<Number>(curr))) return bfalse; \
          prev = curr; \
        } \
        return btrue; \
      });
    declareBinary("<", <);
    declareBinary(">", <);
    declareBinary("<=", <=);
    declareBinary(">=", >=);
    declareBinary("=", ==);
    #undef declareBinary

    // [√]
    primNames["print"] = addPrim(true, [this] (SExpr*, SExpr* e) -> Result {
      String res = e->toString();
      return pool.emplaceBack(res);
    });

    // [?] TODO: output to ostream
    primNames["display"] = addPrim(true, [this] (SExpr*, SExpr* e) -> Result {
      const auto [head, tail] = expect<Cons>(e);
      String res = expect<String>(head);
      return pool.emplaceBack(res);
    });

    // =========================
    // ApiMu-specific procedures
    // =========================

    // [!] Conversions between lists and native objects (`Expr`, `Context`)
    primNames["list->Expr"] = addPrim(true, [this] (SExpr*, SExpr* e) -> Result {
      return pool.emplaceBack(Native{ SExprToExpr(expect<Cons>(e).head, epool) });
    });
    primNames["Expr->list"] = addPrim(true, [this] (SExpr*, SExpr* e) -> Result {
      return ExprToSExpr(expectNative<const Expr*>(expect<Cons>(e).head), pool);
    });
    // ...

    primNames["Print"] = addPrim(true, [this] (SExpr*, SExpr* e) -> Result {
      return pool.emplaceBack(expectNative<const Expr*>(expect<Cons>(e).head)->toString(ctx));
    });
    primNames["PrintFOL"] = addPrim(true, [this] (SExpr*, SExpr* e) -> Result {
      return pool.emplaceBack(Core::FOLForm::fromExpr(expectNative<const Expr*>(expect<Cons>(e).head)).toString(ctx));
    });
    primNames["CheckType"] = addPrim(true, [this] (SExpr*, SExpr* e) -> Result {
      try {
        auto res = expectNative<const Expr*>(expect<Cons>(e).head)->checkType(ctx, epool);
        return pool.emplaceBack(Native{ res });
      } catch (std::runtime_error& ex) {
        return pool.emplaceBack(String{ ex.what() });
      }
    });

    // [?] TEMP CODE
    primNames["MakeBound"] = addPrim(true, [this] (SExpr*, SExpr* e) -> Result {
      const auto [h, t] = expect<Cons>(e);
      const auto [h1, t1] = expect<Cons>(t);
      auto id = static_cast<uint64_t>(expect<Number>(h1));
      const auto res = SExprToExpr(h, epool)->makeBound(id, epool);
      return ExprToSExpr(res, pool);
    });
    primNames["MakeReplace"] = addPrim(true, [this] (SExpr*, SExpr* e) -> Result {
      const auto [h, t] = expect<Cons>(e);
      const auto [h1, t1] = expect<Cons>(t);
      const auto res = SExprToExpr(h, epool)->makeReplace(SExprToExpr(h1, epool), epool);
      return ExprToSExpr(res, pool);
    });

    // END OF FLATBREAD CODE (摊大饼结束)
  }

  // Environment entries are stored as lists of two elements.
  SExpr* Environment::extend(SExpr* env, const std::string& sym, SExpr* e) {
    #define cons pool.emplaceBack
    return cons(cons(pool.emplaceBack(Symbol{ sym }), cons(e, nil)), env);
    #undef cons
  }

  SExpr* Environment::lookup(SExpr* env, const std::string& sym) {
    for (auto it = env; holds<Cons>(it); it = get<Cons>(it).tail) {
      const auto curr = get<Cons>(it).head;
      if (holds<Cons>(curr)) {
        const auto [lhs, t] = get<Cons>(curr);
        const auto [rhs, _] = get<Cons>(t);
        if (holds<Symbol>(lhs) && get<Symbol>(lhs).s == sym)
          return (holds<Undefined>(rhs))? nullptr : rhs;
      }
    }
    return nullptr;
  }

  SExpr* Environment::eval(SExpr* env, SExpr* e) {
    while (true) {
      // Evaluate current `e` under current `env`

      if (holds<Symbol>(e)) {
        // Symbols: evaluate to their bound values
        string sym = get<Symbol>(e).s;
        const auto val = lookup(env, sym);
        if (val) return val;
        const auto it = primNames.find(sym);
        if (it != primNames.end()) return pool.emplaceBack(Builtin{ it->second });
        throw PartialEvalError("unbound symbol \"" + sym + "\"", e);

      } else if (holds<Cons>(e)) {
        // Non-empty lists: evaluate as function application
        try {
          const auto [head, tail] = get<Cons>(e);
          const auto ehead = eval(env, head);

          if (holds<Builtin>(ehead)) {
            // Primitive function application
            const auto [evalParams, f] = prim[get<Builtin>(ehead).index];
            const auto res = f(env, evalParams? evalList(env, tail) : tail);
            // No tail call, return
            if (!res.env) return res.e;
            // Tail call
            env = res.env;
            e = res.e;
            continue;
          }

          if (holds<Closure>(ehead)) {
            // Lambda function application
            const auto cl = get<Closure>(ehead);
            const auto params = evalList(env, tail);
            // Evaluate body as tail call
            env = cl.env;
            bool matched = matchSimple(params, cl.formal, env);
            if (!matched) throw EvalError("pattern matching failed: " + cl.formal->toString() + " ?= " + params->toString(), tail, e);
            e = evalListExceptLast(env, cl.es);
            continue;
          }

          throw EvalError("head element " + ehead->toString() + " is not a function", head, e);

        } catch (PartialEvalError& ex) {
          // "Decorate" partial exceptions with more context, and rethrow a (complete) exception
          throw EvalError(ex.what(), ex.at, e);
        }

      } else {
        // Everything else: evaluates to itself
        return e;
      }
    }
  }

  // Evaluates elements in a list (often used as parameters)
  SExpr* Environment::evalList(SExpr* env, SExpr* e) {
    if (holds<Nil>(e)) return e;
    else if (holds<Cons>(e)) {
      const auto [head, tail] = get<Cons>(e);
      const auto ehead = eval(env, head);
      const auto etail = evalList(env, tail);
      return (ehead == head && etail == tail)? e : pool.emplaceBack(ehead, etail);
    }
    throw PartialEvalError("expected list", e);
  }

  // Executes elements in a list, except the last one (for tail call optimization)
  // Returns the last one unevaluated, or `#undefined` if list is empty
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

  // Evaluates a quasiquoted list
  SExpr* Environment::evalQuasiquote(SExpr* env, SExpr* e) {
    if (holds<Cons>(e)) {
      const auto [head, tail] = get<Cons>(e);
      if (*head == SExpr(Symbol{ "unquote" })) {
        if (holds<Cons>(tail)) return eval(env, get<Cons>(tail).head);
        else throw PartialEvalError("expected list", tail);
      }
      const auto ehead = evalQuasiquote(env, head);
      const auto etail = evalQuasiquote(env, tail);
      return (ehead == head && etail == tail)? e : pool.emplaceBack(ehead, etail);
    }
    return e;
  }

  SExpr* ExprToSExpr(const Expr* e, Allocator<SExpr>& pool) {
    using enum Expr::Tag;
    using enum Expr::SortTag;
    using enum Expr::VarTag;
    #define cons   pool.emplaceBack
    #define nil    pool.emplaceBack(Nil{})
    #define sym(s) pool.emplaceBack(Symbol{ s })
    #define str(s) pool.emplaceBack(String{ s })
    #define num(n) pool.emplaceBack(Number(n))
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
          case VBound: return cons(sym("Var"), cons(sym("Bound"), cons(num(e->var.id), nil)));
          case VFree:  return cons(sym("Var"), cons(sym("Free"),  cons(num(e->var.id), nil)));
          case VMeta:  return cons(sym("Var"), cons(sym("Meta"),  cons(num(e->var.id), nil)));
        }
        break;
      case App: return cons(sym("App"),                     cons(ExprToSExpr(e->app.l, pool), cons(ExprToSExpr(e->app.r, pool), nil)));
      case Lam: return cons(sym("Lam"), cons(str(e->lam.s), cons(ExprToSExpr(e->lam.t, pool), cons(ExprToSExpr(e->lam.r, pool), nil))));
      case Pi:  return cons(sym("Pi"),  cons(str(e->pi.s),  cons(ExprToSExpr(e->pi.t,  pool), cons(ExprToSExpr(e->pi.r,  pool), nil))));
    } exhaustive;
    #undef cons
    #undef nil
    #undef sym
    #undef str
    #undef num
  }

  const Expr* SExprToExpr(SExpr* e, Allocator<Expr>& pool) {
    using enum Expr::Tag;
    #define expr pool.emplaceBack
    const auto [h, t] = expect<Cons>(e);
    string sym = expect<Symbol>(h).s;
    if (sym == "Sort") {
      const auto [h1, t1] = expect<Cons>(t);
      expect<Nil>(t1);
      string tag = expect<Symbol>(h1).s;
      if      (tag == "Prop") return expr(Expr::SProp);
      else if (tag == "Type") return expr(Expr::SType);
      else if (tag == "Kind") return expr(Expr::SKind);
      else throw PartialEvalError(R"(tag must be "Prop", "Type" or "Kind")", h1);
    } else if (sym == "Var") {
      const auto [h1, t1] = expect<Cons>(t);
      const auto [h2, t2] = expect<Cons>(t1);
      expect<Nil>(t2);
      string tag = expect<Symbol>(h1).s;
      Number id = expect<Number>(h2);
      if (id < 0) throw PartialEvalError(R"(variable id must be nonnegative)", h2);
      if      (tag == "Bound") return expr(Expr::VBound, static_cast<uint64_t>(id));
      else if (tag == "Free")  return expr(Expr::VFree,  static_cast<uint64_t>(id));
      else if (tag == "Meta")  return expr(Expr::VMeta,  static_cast<uint64_t>(id));
      else throw PartialEvalError(R"(tag must be "Bound", "Free" or "Meta")", h1);
    } else if (sym == "App") {
      const auto [h1, t1] = expect<Cons>(t);
      const auto [h2, t2] = expect<Cons>(t1);
      expect<Nil>(t2);
      return expr(SExprToExpr(h1, pool), SExprToExpr(h2, pool));
    } else if (sym == "Lam") {
      const auto [h1, t1] = expect<Cons>(t);
      const auto [h2, t2] = expect<Cons>(t1);
      const auto [h3, t3] = expect<Cons>(t2);
      expect<Nil>(t3);
      return expr(Expr::LLam, expect<String>(h1), SExprToExpr(h2, pool), SExprToExpr(h3, pool));
    } else if (sym == "Pi") {
      const auto [h1, t1] = expect<Cons>(t);
      const auto [h2, t2] = expect<Cons>(t1);
      const auto [h3, t3] = expect<Cons>(t2);
      expect<Nil>(t3);
      return expr(Expr::PPi, expect<String>(h1), SExprToExpr(h2, pool), SExprToExpr(h3, pool));
    } else throw PartialEvalError(R"(symbol must be "Sort", "Var", "App", "Lam" or "Pi")", h);
    #undef expr
  }

}
