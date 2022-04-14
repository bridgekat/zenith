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
    static const SExpr* extend(const SExpr* env, const std::string& sym, const SExpr* e, Core::Allocator<SExpr>& pool);
    static const SExpr* find(const SExpr* env, const std::string& sym);

    // This will store intermediate and final results on `this.pool`.
    const SExpr* evalStatement(const SExpr* e) {
      e = e->clone(pool);
      try { return eval(globalEnv, e); }
      catch (EvalError& ex) { ex.e = e; throw ex; }
    }

  private:
    // `env != nullptr` means that `e` still needs to be evaluated under `env` (for proper tail recursion).
    struct Result {
      const SExpr* env, * e;
      Result(const SExpr* e): env(nullptr), e(e) {};
      Result(const SExpr* env, const SExpr* e): env(env), e(e) {};
    };
    using PrimitiveProc = std::function<Result(const SExpr*, const SExpr*)>;

    Core::Allocator<SExpr> pool;
    std::unordered_map<std::string, PrimitiveProc> forms, procs;
    const SExpr* globalEnv;

    const SExpr* eval(const SExpr* env, const SExpr* e);
    const SExpr* evalList(const SExpr* env, const SExpr* e);
    const SExpr* execListTailcall(const SExpr* env, const SExpr* e);
    const SExpr* evalUnquote(const SExpr* env, const SExpr* e);
  };

}

#endif // ENVIRONMENT_HPP_
