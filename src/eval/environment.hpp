// Eval :: EvalError, Environment

#ifndef ENVIRONMENT_HPP_
#define ENVIRONMENT_HPP_

#include <string>
#include <unordered_map>
#include <utility>
#include <functional>
#include "sexpr.hpp"


namespace Eval {

  struct EvalError: public std::runtime_error {
    const SExpr* at;
    const SExpr* e;
    explicit EvalError(const std::string& s, const SExpr* at, const SExpr* e = nullptr):
      std::runtime_error(s), at(at), e(e? e : at) {}
    EvalError(const EvalError&) = default;
    EvalError& operator=(const EvalError&) = default;
  };

  class Environment {
  public:
    Environment();
    Environment(const Environment&) = default;
    Environment& operator=(const Environment&) = default;
    ~Environment() = default;

    // Far less efficient than hash tries (HAMTs), but should be enough for current purpose!
    static SExpr* extend(SExpr* env, const std::string& sym, SExpr* e, Core::Allocator<SExpr>& pool);
    static SExpr* find(SExpr* env, const std::string& sym);

    // This will store intermediate and final results on `this.pool`.
    SExpr* evalStatement(const SExpr* e) {
      auto clone = e->clone(pool);
      try { return eval(globalEnv, clone); }
      catch (EvalError& ex) { ex.e = clone; throw ex; }
    }

  private:
    // `env != nullptr` means that `e` still needs to be evaluated under `env` (for proper tail recursion).
    struct Result {
      SExpr* env, * e;
      Result(SExpr* e): env(nullptr), e(e) {};
      Result(SExpr* env, SExpr* e): env(env), e(e) {};
    };
    using PrimitiveProc = std::function<Result(SExpr*, SExpr*)>;

    Core::Allocator<SExpr> pool;
    std::unordered_map<std::string, PrimitiveProc> forms, procs;
    SExpr* globalEnv;
    SExpr* const undefined;

    SExpr* eval(SExpr* env, SExpr* e);
    SExpr* evalList(SExpr* env, SExpr* e);
    SExpr* evalListExceptLast(SExpr* env, SExpr* e);
    SExpr* evalQuasiquote(SExpr* env, SExpr* e);
  };

}

#endif // ENVIRONMENT_HPP_
