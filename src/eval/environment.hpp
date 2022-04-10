// Eval :: Environment, EvalError

#ifndef ENVIRONMENT_HPP_
#define ENVIRONMENT_HPP_

#include <string>
#include <unordered_map>
#include <functional>
#include "sexpr.hpp"


namespace Eval {

  class Environment {
  public:
    using Proc = std::function<const SExpr*(const SExpr*, Environment&, Core::Allocator<SExpr>&)>;

    Core::Allocator<SExpr> pool;
    std::unordered_map<std::string, Proc> forms, procs;
    std::unordered_map<std::string, const SExpr*> vars;

    Environment();
    const SExpr* evalAll(const SExpr* e);
    const SExpr* eval(const SExpr* e);
  };

  struct EvalError: public std::runtime_error {
    const SExpr* at;
    const SExpr* e;
    explicit EvalError(const std::string& s, const SExpr* at, const SExpr* e = nullptr):
      std::runtime_error(s), at(at), e(e? e : at) {}
    EvalError(const EvalError&) = default;
    EvalError& operator=(const EvalError&) = default;
  };

}

#endif // ENVIRONMENT_HPP_
