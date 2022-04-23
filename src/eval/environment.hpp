// Eval :: EvalError, Environment...

#ifndef ENVIRONMENT_HPP_
#define ENVIRONMENT_HPP_

#include <string>
#include <vector>
#include <unordered_map>
#include <utility>
#include <functional>
#include <core.hpp>
#include "sexpr.hpp"


namespace Eval {

  struct EvalError: public std::runtime_error {
    const SExpr* at;
    const SExpr* e;
    EvalError(const std::string& s, const SExpr* at, const SExpr* e): std::runtime_error(s), at(at), e(e) {}
    EvalError(const EvalError&) = default;
    EvalError& operator=(const EvalError&) = default;
  };

  class Environment {
  public:
    Environment();
    Environment(const Environment&) = delete;
    Environment(Environment&&) = delete;
    Environment& operator=(const Environment&) = delete;
    Environment& operator=(Environment&&) = delete;
    ~Environment() = default;

    // This will store intermediate and final results on `this.pool`.
    SExpr* evalStatement(const SExpr* e) {
      return eval(globalEnv, e->clone(pool, nil, undefined));
    }

  private:
    // `env != nullptr` means that `e` still needs to be evaluated under `env` (for proper tail recursion).
    struct Result {
      SExpr* env, * e;
      Result(SExpr* e): env(nullptr), e(e) {};
      Result(SExpr* env, SExpr* e): env(env), e(e) {};
    };

    std::vector<std::pair<bool, std::function<Result(SExpr*, SExpr*)>>> prim;
    std::unordered_map<std::string, size_t> primNames;

    Core::Allocator<SExpr> pool;
    Core::Allocator<Core::Expr> epool;
    Core::FOLContext globalCtx;

    SExpr* globalEnv;
    SExpr* nil, * undefined;

    size_t addPrim(bool evalParams, std::function<Result(SExpr*, SExpr*)> f) {
      size_t res = prim.size();
      prim.emplace_back(evalParams, f);
      return res;
    }

    bool matchSimple(SExpr* e, SExpr* pat, SExpr*& env);
    bool matchFull(SExpr* e, SExpr* pat, SExpr*& env, bool quoteMode = false);

    // Far less efficient than hash tries (HAMTs), but should be enough for current purpose!
    SExpr* extend(SExpr* env, const std::string& sym, SExpr* e);
    SExpr* lookup(SExpr* env, const std::string& sym);

    SExpr* eval(SExpr* env, SExpr* e);
    SExpr* evalList(SExpr* env, SExpr* e);
    SExpr* evalListExceptLast(SExpr* env, SExpr* e);
    SExpr* evalQuasiquote(SExpr* env, SExpr* e);
  };

  // Build an S-expression representation of a logical expression (lifetime bounded by `pool`).
  SExpr* ExprToSExpr(const Core::Expr* e, Core::Allocator<SExpr>& pool);

  // Try convert S-expression to logical expression (lifetime bounded by `pool`).
  // Throws `EvalError` if not well-formed.
  const Core::Expr* SExprToExpr(SExpr* e, Core::Allocator<Core::Expr>& pool);

}

#endif // ENVIRONMENT_HPP_
