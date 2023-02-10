#ifndef APIMU_EVAL_EXTENDED_EVALUATOR_HPP
#define APIMU_EVAL_EXTENDED_EVALUATOR_HPP

#include <core/expr.hpp>
#include <core/fol/fol.hpp>
#include "evaluator.hpp"

namespace apimu::eval {
#include "macros_open.hpp"

  class ExtendedEvaluator: public Evaluator {
  public:
    ExtendedEvaluator();

  private:
    core::FOLContext ctx;
    Allocator<core::Expr> epool;

    auto exprTree(core::Expr const* e) -> Tree*;
    auto treeExpr(Tree* e) -> core::Expr const*;
  };

#include "macros_close.hpp"
}

#endif // APIMU_EVAL_EXTENDED_EVALUATOR_HPP
