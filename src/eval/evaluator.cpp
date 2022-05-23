#include "evaluator.hpp"


namespace Eval {

  using std::string;
  using std::vector;
  using std::pair;
  using std::optional;
  using Core::Expr, Core::Allocator;
  using Parsing::Token, Parsing::EarleyParser;


  bool operator==(const EarleyParser::Location& a, const EarleyParser::Location& b) {
    return a.pos == b.pos && a.i == b.i;
  }

  class Resolver {
  public:
    const vector<Token>& sentence;
    const vector<vector<EarleyParser::LinkedState>>& forest;
    vector<vector<optional<vector<Tree*>>>> res;
    const size_t numResults = 64, maxDepth = 4096;

    Resolver(const vector<Token>& sentence, const vector<vector<EarleyParser::LinkedState>>& forest):
      sentence(sentence), forest(forest) {}

    vector<Tree*> operator()() {
      res.resize(forest.size());
      for (size_t pos = 0; pos < forest.size(); pos++) res[pos].resize(forest[pos].size());
      // dfs(); // #####
    }
  };

  Tree* Evaluator::evalNextStatement() {
    const auto& opt = parser.nextSentence();
    if (!opt) return nullptr;
    // #####
  }

  vector<Tree*> Evaluator::resolveParse(EarleyParser::Location loc, size_t numResults, size_t maxDepth) const {
    vector<Tree*> res;
    if (maxDepth == 0) return res;
    const auto& [state, links] = parser.getForest()[loc.pos][loc.i];
    for (const auto& [next, child]: links) {
      vector<Tree*> nextRes = resolveParse(next, numResults, maxDepth - 1);
      if (!nextRes.empty()) {
        vector<Tree*> childRes;
        if (child == EarleyParser::Leaf) {
          // #####
        } else {
          childRes = resolveParse(child, numResults, maxDepth - 1);
        }
        // #####
      }
      // #####
    }
    // #####
  }

  // Throw this when you don't know about the parent expression,
  // or when you want the parent call to `eval()` to provide context.
  struct PartialEvalError: public EvalError {
    PartialEvalError(const std::string& s, const Tree* at): EvalError(s, at, at) {}
  };

  // A shortcut for `std::holds_alternative<T>(e->v)`
  template <typename T>
  bool holds(Tree* e) noexcept { return std::holds_alternative<T>(e->v); }

  // A shortcut for `std::get<T>(e->v)` (terminates on failure)
  template <typename T>
  T& get(Tree* e) noexcept { return std::get<T>(e->v); }

  // Convenient pattern-matching functions (throw customized exceptions on failure)
  template <typename T>
  T& expect(Tree*) { unreachable; }
  #define declareExpect(T, msg) \
    template <> \
    T& expect<T>(Tree* e) { \
      try { return std::get<T>(e->v); } \
      catch (std::bad_variant_access&) { throw PartialEvalError((msg ", got ") + e->toString(), e); } \
    }
  declareExpect(Nil,     "expected end-of-list")
  declareExpect(Cons,    "expected non-empty list")
  declareExpect(Symbol,  "expected symbol")
  declareExpect(Nat64,   "expected number")
  declareExpect(String,  "expected string")
  declareExpect(Bool,    "expected boolean")
  declareExpect(Closure, "expected function")
  declareExpect(Native,  "expected native type")
  #undef declareExpect

  template <typename T>
  T expectNative(Tree* e) {
    try { return std::any_cast<T>(expect<Native>(e).val); }
    catch (std::bad_any_cast& ex) { throw PartialEvalError(string("native type mismatch: ") + ex.what(), e); }
  }

  // Match an Tree against another Tree (pattern)
  // See: https://github.com/digama0/mm0/blob/master/mm0-hs/mm1.md#syntax-forms
  // (Continuation, `__k`, `and`, `or`, `not` and `pred?` patterns are not implemented)
  bool Evaluator::match(Tree* e, Tree* pat, Tree*& env, bool quoteMode) {
    if (holds<Symbol>(pat) && !quoteMode) {
      string sym = get<Symbol>(pat).name;
      if (sym != "_") env = extend(env, sym, e);
      return true;
    }
    if (holds<Cons>(pat)) {
      const auto& [h, t] = get<Cons>(pat);
      if (holds<Symbol>(h)) {
        string sym = get<Symbol>(h).name;
        if (sym == "quote" && !quoteMode) return match(e, expect<Cons>(t).head, env, true); // Enter quote mode
        if (sym == "unquote" && quoteMode) return match(e, expect<Cons>(t).head, env, false); // Leave quote mode
        if (sym == "...") return holds<Nil>(e) || holds<Cons>(e);
      }
      return holds<Cons>(e) &&
        match(get<Cons>(e).head, h, env, quoteMode) &&
        match(get<Cons>(e).tail, t, env, quoteMode);
    }
    return *e == *pat;
  }

  // Initialize with built-in forms and procedures
  // See: https://github.com/digama0/mm0/blob/master/mm0-hs/mm1.md#syntax-forms
  // See: https://github.com/digama0/mm0/blob/master/mm0-hs/mm1.md#Prim-functions
  Evaluator::Evaluator(): prims(), primNames(), pool(), // epool(), globalCtx(),
      globalEnv(pool.emplaceBack(Nil{})),
      nil(pool.emplaceBack(Nil{})), unit(pool.emplaceBack(Unit{})),
      lexer(), parser(lexer) {
    // BEGIN FLATBREAD CODE (开始摊大饼)

    // Commonly used constants
    // const auto nzero  = pool.emplaceBack(Nat64{ 0 });
    // const auto sempty = pool.emplaceBack(String{ "" });
    const auto btrue  = pool.emplaceBack(Bool{ true });
    const auto bfalse = pool.emplaceBack(Bool{ false });

    // ===============
    // Primitive forms
    // ===============

    // [√] Quasiquotation
    primNames["quote"] = addPrim(false, [this] (Tree* env, Tree* e) -> Result { return evalQuasiquote(env, expect<Cons>(e).head); });
    primNames["unquote"] = addPrim(false, [this] (Tree* env, Tree* e) -> Result { return eval(env, expect<Cons>(e).head); });

    // [√] Currently we don't have a `let`, and this is just a synonym of `let*`...
    primNames["let"] = addPrim(false, [this] (Tree* env, Tree* e) -> Result {
      const auto& [defs, es] = expect<Cons>(e);
      for (auto it = defs; holds<Cons>(it); it = get<Cons>(it).tail) {
        const auto& [lhs, t] = expect<Cons>(get<Cons>(it).head);
        if (holds<Cons>(lhs)) {
          // Function definition
          const auto& [sym, formal] = get<Cons>(lhs);
          const auto& body = t;
          env = extend(env, expect<Symbol>(sym).name, pool.emplaceBack(Closure{ env, formal, body }));
        } else {
          // General definition (ignores more arguments)
          const auto& sym = lhs;
          const auto& [val, _] = expect<Cons>(t);
          env = extend(env, expect<Symbol>(sym).name, eval(env, val));
        }
      }
      return { env, evalListExceptLast(env, es) };
    });

    // [√] Currently we don't have a `letrec`, and this is just a synonym of `letrec*`...
    primNames["letrec"] = addPrim(false, [this] (Tree* env, Tree* e) -> Result {
      const auto& [defs, es] = expect<Cons>(e);
      // Add #unit (placeholder) bindings
      vector<Tree**> refs;
      for (auto it = defs; holds<Cons>(it); it = get<Cons>(it).tail) {
        const auto& [lhs, t] = expect<Cons>(get<Cons>(it).head);
        if (holds<Cons>(lhs)) {
          // Function definition
          const auto& [sym, _] = get<Cons>(lhs);
          env = extend(env, expect<Symbol>(sym).name, unit);
        } else {
          // General definition (ignores more arguments)
          const auto& sym = lhs;
          env = extend(env, expect<Symbol>(sym).name, unit);
        }
        refs.push_back(&get<Cons>(get<Cons>(get<Cons>(env).head).tail).head); // Will always succeed due to the recent `extend`
      }
      // Sequentially evaluate and assign
      size_t i = 0;
      for (auto it = defs; holds<Cons>(it); it = get<Cons>(it).tail) {
        const auto& [lhs, t] = expect<Cons>(get<Cons>(it).head);
        if (holds<Cons>(lhs)) {
          // Function definition
          const auto& [_, formal] = get<Cons>(lhs);
          const auto& body = t;
          *refs[i++] = pool.emplaceBack(Closure{ env, formal, body });
        } else {
          // General definition (ignores more arguments)
          const auto& [val, _] = expect<Cons>(t);
          *refs[i++] = eval(env, val);
        }
      }
      return { env, evalListExceptLast(env, es) };
    });

    // [√] This modifies nodes reachable through `env` (which prevents making `Tree*` into const pointers)
    // Ignores more arguments
    primNames["set!"] = addPrim(false, [this] (Tree* env, Tree* e) -> Result {
      const auto& [sym, t] = expect<Cons>(e);
      const auto& [exp, _] = expect<Cons>(t);
      const auto& val = eval(env, exp);
      string s = expect<Symbol>(sym).name;
      for (auto it = env; holds<Cons>(it); it = get<Cons>(it).tail) {
        const auto& curr = get<Cons>(it).head;
        if (holds<Cons>(curr)) {
          auto& [lhs, t1] = get<Cons>(curr);
          auto& [rhs, t2] = get<Cons>(t1);
          if (holds<Symbol>(lhs) && get<Symbol>(lhs).name == s) { rhs = val; return unit; }
        }
      }
      throw PartialEvalError("unbound symbol \"" + s + "\"", sym);
    });

    // [√]
    primNames["lambda"] = addPrim(false, [this] (Tree* env, Tree* e) -> Result {
      const auto& [formal, es] = expect<Cons>(e);
      return pool.emplaceBack(Closure{ env, formal, es });
    });

    // [√] Ignores more arguments
    primNames["if"] = addPrim(false, [this] (Tree* env, Tree* e) -> Result {
      const auto& [test, t] = expect<Cons>(e);
      const auto& [iftrue, t1] = expect<Cons>(t);
      const auto& iffalse = (holds<Cons>(t1)? get<Cons>(t1).head : unit);
      bool result = expect<Bool>(eval(env, test)).val;
      return { env, result? iftrue : iffalse };
    });

    // [√]
    primNames["match"] = addPrim(false, [this] (Tree* env, Tree* e) -> Result {
      const auto& [head, clauses] = expect<Cons>(e);
      const auto& target = eval(env, head);
      for (auto it = clauses; holds<Cons>(it); it = get<Cons>(it).tail) {
        const auto& [pat, t1] = expect<Cons>(get<Cons>(it).head);
        Tree* newEnv = env;
        if (match(target, pat, newEnv)) {
          const auto& [expr, _] = expect<Cons>(t1);
          return { newEnv, expr };
        }
      }
      // All failed, throw exception
      string msg = "nonexhaustive patterns: { ";
      bool first = true;
      for (auto it = clauses; holds<Cons>(it); it = get<Cons>(it).tail) {
        const auto& [pat, _] = expect<Cons>(get<Cons>(it).head);
        if (!first) msg += ", ";
        first = false;
        msg += pat->toString();
      }
      msg += " } ?= " + target->toString();
      throw PartialEvalError(msg, clauses);
    });

    // [√] Global definitions will become effective only on the next statement...
    // For local definitions, use `letrec*`.
    primNames["define"] = addPrim(false, [this] (Tree* env, Tree* e) -> Result {
      const auto& [lhs, t] = expect<Cons>(e);
      if (holds<Cons>(lhs)) {
        // Function definition
        const auto& [sym, formal] = get<Cons>(lhs);
        const auto& es = t;
        // Add an #unit (placeholder) binding before evaluation
        env = extend(env, expect<Symbol>(sym).name, unit);
        // Evaluate and assign
        const auto& self = pool.emplaceBack(Closure{ env, formal, es });
        get<Cons>(get<Cons>(get<Cons>(env).head).tail).head = self; // Will always succeed due to the recent `extend`
        globalEnv = extend(globalEnv, expect<Symbol>(sym).name, self);
      } else {
        // General definition (ignores more arguments)
        const auto& sym = lhs;
        const auto& [val, _] = expect<Cons>(t);
        globalEnv = extend(globalEnv, expect<Symbol>(sym).name, eval(env, val));
      }
      return unit;
    });

    // [√]
    primNames["begin"] = addPrim(false, [this] (Tree* env, Tree* e) -> Result {
      return { env, evalListExceptLast(env, e) };
    });

    // ====================
    // Primitive procedures
    // ====================

    // [√]
    primNames["eval"] = addPrim(true, [] (Tree* env, Tree* e) -> Result {
      const auto& [head, tail] = expect<Cons>(e);
      if (holds<Cons>(tail)) env = expect<Cons>(tail).head;
      return { env, head }; // Let it restart and evaluate
    });
    primNames["get-env"] = addPrim(true, [] (Tree* env, Tree*) -> Result { return env; });
    primNames["get-global-env"] = addPrim(true, [this] (Tree*, Tree*) -> Result { return globalEnv; });
    primNames["set-global-env"] = addPrim(true, [this] (Tree*, Tree* e) -> Result { globalEnv = expect<Cons>(e).head; return unit; });

    // [√]
    /*
    primNames["+"] = addPrim(true, [this] (Tree*, Tree* e) -> Result {
      Number res = 0;
      for (auto it = e; holds<Cons>(it); it = get<Cons>(it).tail) res += expect<Number>(get<Cons>(it).head);
      return pool.emplaceBack(res);
    });
    primNames["-"] = addPrim(true, [this] (Tree*, Tree* e) -> Result {
      const auto& [head, tail] = expect<Cons>(e); e = tail;
      Number res = expect<Number>(head);
      if (!holds<Cons>(e)) return pool.emplaceBack(-res);
      for (auto it = e; holds<Cons>(it); it = get<Cons>(it).tail) res -= expect<Number>(get<Cons>(it).head);
      return pool.emplaceBack(res);
    });
    primNames["*"] = addPrim(true, [this] (Tree*, Tree* e) -> Result {
      Number res = 1;
      for (auto it = e; holds<Cons>(it); it = get<Cons>(it).tail) res *= expect<Number>(get<Cons>(it).head);
      return pool.emplaceBack(res);
    });
    primNames["/"] = addPrim(true, [this] (Tree*, Tree* e) -> Result {
      const auto& [head, tail] = expect<Cons>(e); e = tail;
      Number res = expect<Number>(head);
      for (auto it = e; holds<Cons>(it); it = get<Cons>(it).tail) res /= expect<Number>(get<Cons>(it).head);
      return pool.emplaceBack(res);
    });
    primNames["%"] = addPrim(true, [this] (Tree*, Tree* e) -> Result {
      const auto& [head, tail] = expect<Cons>(e); e = tail;
      Number res = expect<Number>(head);
      for (auto it = e; holds<Cons>(it); it = get<Cons>(it).tail) res %= expect<Number>(get<Cons>(it).head);
      return pool.emplaceBack(res);
    });

    // [√]
    #define declareBinary(sym, op) \
      primNames[sym] = addPrim(true, [bfalse, btrue] (Tree*, Tree* e) -> Result { \
        const auto& [head, tail] = expect<Cons>(e); \
        auto prev = head; \
        for (auto it = tail; holds<Cons>(it); it = get<Cons>(it).tail) { \
          const auto& curr = get<Cons>(it).head; \
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
    */

    // [√]
    primNames["print"] = addPrim(true, [this] (Tree*, Tree* e) -> Result {
      String res{ e->toString() };
      return pool.emplaceBack(res);
    });

    // [?] TODO: output to ostream
    primNames["display"] = addPrim(true, [this] (Tree*, Tree* e) -> Result {
      const auto& [head, tail] = expect<Cons>(e);
      String res = expect<String>(head);
      return pool.emplaceBack(res);
    });

    // =========================
    // ApiMu-specific procedures
    // =========================

    /*
    #define cons   pool.emplaceBack
    #define nil    pool.emplaceBack(Nil{})
    #define sym(s) pool.emplaceBack(Symbol{ s })
    #define str(s) pool.emplaceBack(String{ s })
    #define num(n) pool.emplaceBack(Number{ n })
    #define obj(o) pool.emplaceBack(Native{ o })

    // [!] Conversions between lists and native objects (`Expr`, `Context`)
    primNames["list->Expr"] = addPrim(true, [this] (Tree*, Tree* e) -> Result {
      return obj(TreeExpr(expect<Cons>(e).head, epool));
    });
    primNames["Expr->list"] = addPrim(true, [this] (Tree*, Tree* e) -> Result {
      return ExprTree(expectNative<const Expr*>(expect<Cons>(e).head), pool);
    });
    // ...

    // [?] TEMP CODE
    primNames["ContextSize"] = addPrim(true, [this] (Tree*, Tree*) -> Result {
      return num(static_cast<Number>(globalCtx.size()));
    });
    primNames["ContextGet"] = addPrim(true, [this] (Tree*, Tree* e) -> Result {
      auto i = expect<Number>(expect<Cons>(e).head);
      if (i >= 0) {
        size_t index = static_cast<size_t>(i);
        if (index < globalCtx.size()) return cons(str(globalCtx.identifier(index)), cons(obj(globalCtx[index]), nil));
      }
      return unit;
    });
    primNames["ContextPush"] = addPrim(true, [this] (Tree*, Tree* e) -> Result {
      const auto& [lhs, t] = expect<Cons>(expect<Cons>(e).head);
      const auto& [rhs, _] = expect<Cons>(t);
      string s = expect<String>(lhs);
      const Expr* expr = expectNative<const Expr*>(rhs);
      try { globalCtx.pushAssumption(s, expr); return unit; }
      catch (std::runtime_error& ex) { return str(ex.what()); }
    });
    primNames["ContextPop"] = addPrim(true, [this] (Tree*, Tree*) -> Result {
      try { globalCtx.pop(); return unit; }
      catch (std::runtime_error& ex) { return str(ex.what()); }
    });
    primNames["Expr.Print"] = addPrim(true, [this] (Tree*, Tree* e) -> Result {
      return str(expectNative<const Expr*>(expect<Cons>(e).head)->toString(globalCtx));
    });
    primNames["Expr.PrintFOL"] = addPrim(true, [this] (Tree*, Tree* e) -> Result {
      return str(Core::FOLForm::fromExpr(expectNative<const Expr*>(expect<Cons>(e).head)).toString(globalCtx));
    });
    primNames["Expr.CheckType"] = addPrim(true, [this] (Tree*, Tree* e) -> Result {
      try { return obj(expectNative<const Expr*>(expect<Cons>(e).head)->checkType(globalCtx, epool)); }
      catch (std::runtime_error& ex) { return str(ex.what()); }
    });

    // [?] TEMP CODE
    primNames["Expr.MakeBound"] = addPrim(true, [this] (Tree*, Tree* e) -> Result {
      const auto& [h, t] = expect<Cons>(e);
      const auto& [h1, t1] = expect<Cons>(t);
      const auto id = static_cast<uint64_t>(expect<Number>(h1));
      const auto res = TreeExpr(h, epool)->makeBound(id, epool);
      return ExprTree(res, pool);
    });
    primNames["Expr.MakeReplace"] = addPrim(true, [this] (Tree*, Tree* e) -> Result {
      const auto& [h, t] = expect<Cons>(e);
      const auto& [h1, t1] = expect<Cons>(t);
      const auto res = TreeExpr(h, epool)->makeReplace(TreeExpr(h1, epool), epool);
      return ExprTree(res, pool);
    });

    #undef cons
    #undef nil
    #undef sym
    #undef str
    #undef num
    */

    // END OF FLATBREAD CODE (摊大饼结束)
  }

  // Evaluator entries are stored as lists of two elements.
  Tree* Evaluator::extend(Tree* env, const std::string& sym, Tree* e) {
    #define cons pool.emplaceBack
    return cons(cons(pool.emplaceBack(Symbol{ sym }), cons(e, nil)), env);
    #undef cons
  }

  Tree* Evaluator::lookup(Tree* env, const std::string& sym) {
    for (auto it = env; holds<Cons>(it); it = get<Cons>(it).tail) {
      const auto& curr = get<Cons>(it).head;
      if (!holds<Cons>(curr)) continue;
      const auto& [lhs, t] = get<Cons>(curr);
      if (!holds<Cons>(t)) continue;
      const auto& [rhs, _] = get<Cons>(t);
      if (holds<Symbol>(lhs) && get<Symbol>(lhs).name == sym)
        return (holds<Unit>(rhs))? nullptr : rhs;
    }
    return nullptr;
  }

  Tree* Evaluator::eval(Tree* env, Tree* e) {
    while (true) {
      // Evaluate current `e` under current `env`

      if (holds<Symbol>(e)) {
        // Symbols: evaluate to their bound values
        string sym = get<Symbol>(e).name;
        const auto val = lookup(env, sym);
        if (val) return val;
        const auto it = primNames.find(sym);
        if (it != primNames.end()) return pool.emplaceBack(Prim{ it->second });
        throw PartialEvalError("unbound symbol \"" + sym + "\"", e);

      } else if (holds<Cons>(e)) {
        // Non-empty lists: evaluate as function application
        try {
          const auto& [head, tail] = get<Cons>(e);
          const auto ehead = eval(env, head);

          if (holds<Prim>(ehead)) {
            // Primitive function application
            const auto& [evalParams, f] = prims[get<Prim>(ehead).id];
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
            const auto& cl = get<Closure>(ehead);
            const auto params = evalList(env, tail);
            // Evaluate body as tail call
            env = cl.env;
            bool matched = match(params, cl.formal, env);
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
  Tree* Evaluator::evalList(Tree* env, Tree* e) {
    if (holds<Nil>(e)) return e;
    else if (holds<Cons>(e)) {
      const auto& [head, tail] = get<Cons>(e);
      const auto ehead = eval(env, head);
      const auto etail = evalList(env, tail);
      return (ehead == head && etail == tail)? e : pool.emplaceBack(ehead, etail);
    }
    throw PartialEvalError("expected list", e);
  }

  // Executes elements in a list, except the last one (for tail call optimization)
  // Returns the last one unevaluated, or `#unit` if list is empty
  Tree* Evaluator::evalListExceptLast(Tree* env, Tree* e) {
    for (auto it = e; holds<Cons>(it); it = get<Cons>(it).tail) {
      const auto& [head, tail] = get<Cons>(it);
      if (!holds<Cons>(tail)) {
        expect<Nil>(tail);
        return head;
      }
      eval(env, head);
    }
    expect<Nil>(e);
    return unit;
  }

  // Evaluates a quasiquoted list
  Tree* Evaluator::evalQuasiquote(Tree* env, Tree* e) {
    if (holds<Cons>(e)) {
      const auto& [head, tail] = get<Cons>(e);
      if (*head == Tree(Symbol{ "unquote" })) {
        if (holds<Cons>(tail)) return eval(env, get<Cons>(tail).head);
        else throw PartialEvalError("expected list", tail);
      }
      const auto ehead = evalQuasiquote(env, head);
      const auto etail = evalQuasiquote(env, tail);
      return (ehead == head && etail == tail)? e : pool.emplaceBack(ehead, etail);
    }
    return e;
  }

  /*
  Tree* ExprTree(const Expr* e, Allocator<Tree>& pool) {
    using enum Expr::Tag;
    using enum Expr::SortTag;
    using enum Expr::VarTag;
    #define cons   pool.emplaceBack
    #define nil    pool.emplaceBack(Nil{})
    #define sym(s) pool.emplaceBack(Symbol{ s })
    #define str(s) pool.emplaceBack(String{ s })
    #define num(n) pool.emplaceBack(Number{ n })
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
          case VBound: return cons(sym("Var"), cons(sym("Bound"), cons(num(static_cast<Number>(e->var.id)), nil)));
          case VFree:  return cons(sym("Var"), cons(sym("Free"),  cons(num(static_cast<Number>(e->var.id)), nil)));
          case VMeta:  return cons(sym("Var"), cons(sym("Meta"),  cons(num(static_cast<Number>(e->var.id)), nil)));
        }
        break;
      case App: return cons(sym("App"),                     cons(ExprTree(e->app.l, pool), cons(ExprTree(e->app.r, pool), nil)));
      case Lam: return cons(sym("Lam"), cons(str(e->lam.s), cons(ExprTree(e->lam.t, pool), cons(ExprTree(e->lam.r, pool), nil))));
      case Pi:  return cons(sym("Pi"),  cons(str(e->pi.s),  cons(ExprTree(e->pi.t,  pool), cons(ExprTree(e->pi.r,  pool), nil))));
    } exhaustive;
    #undef cons
    #undef nil
    #undef sym
    #undef str
    #undef num
  }

  const Expr* TreeExpr(Tree* e, Allocator<Expr>& pool) {
    using enum Expr::Tag;
    #define expr pool.emplaceBack
    const auto& [h, t] = expect<Cons>(e);
    string sym = expect<Symbol>(h).s;
    if (sym == "Sort") {
      const auto& [h1, t1] = expect<Cons>(t);
      expect<Nil>(t1);
      string tag = expect<Symbol>(h1).s;
      if      (tag == "Prop") return expr(Expr::SProp);
      else if (tag == "Type") return expr(Expr::SType);
      else if (tag == "Kind") return expr(Expr::SKind);
      else throw PartialEvalError(R"(tag must be "Prop", "Type" or "Kind")", h1);
    } else if (sym == "Var") {
      const auto& [h1, t1] = expect<Cons>(t);
      const auto& [h2, t2] = expect<Cons>(t1);
      expect<Nil>(t2);
      string tag = expect<Symbol>(h1).s;
      Number id = expect<Number>(h2);
      if (id < 0) throw PartialEvalError(R"(variable id must be nonnegative)", h2);
      if      (tag == "Bound") return expr(Expr::VBound, static_cast<uint64_t>(id));
      else if (tag == "Free")  return expr(Expr::VFree,  static_cast<uint64_t>(id));
      else if (tag == "Meta")  return expr(Expr::VMeta,  static_cast<uint64_t>(id));
      else throw PartialEvalError(R"(tag must be "Bound", "Free" or "Meta")", h1);
    } else if (sym == "App") {
      const auto& [h1, t1] = expect<Cons>(t);
      const auto& [h2, t2] = expect<Cons>(t1);
      expect<Nil>(t2);
      return expr(TreeExpr(h1, pool), TreeExpr(h2, pool));
    } else if (sym == "Lam") {
      const auto& [h1, t1] = expect<Cons>(t);
      const auto& [h2, t2] = expect<Cons>(t1);
      const auto& [h3, t3] = expect<Cons>(t2);
      expect<Nil>(t3);
      return expr(Expr::LLam, expect<String>(h1), TreeExpr(h2, pool), TreeExpr(h3, pool));
    } else if (sym == "Pi") {
      const auto& [h1, t1] = expect<Cons>(t);
      const auto& [h2, t2] = expect<Cons>(t1);
      const auto& [h3, t3] = expect<Cons>(t2);
      expect<Nil>(t3);
      return expr(Expr::PPi, expect<String>(h1), TreeExpr(h2, pool), TreeExpr(h3, pool));
    } else throw PartialEvalError(R"(symbol must be "Sort", "Var", "App", "Lam" or "Pi")", h);
    #undef expr
  }
  */

}
