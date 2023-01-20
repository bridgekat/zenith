// Eval :: ExtendedEvaluator

#ifndef EXTENDED_EVALUATOR_HPP_
#define EXTENDED_EVALUATOR_HPP_

#include <core/expr.hpp>
#include <core/fol/fol.hpp>
#include "evaluator.hpp"

namespace Eval {

  class ExtendedEvaluator: public Evaluator {
  public:
    ExtendedEvaluator();

  private:
    Core::FOLContext ctx;
    Allocator<Core::Expr> epool;

    auto exprTree(Core::Expr const* e) -> Tree*;
    auto treeExpr(Tree* e) -> Core::Expr const*;
  };

}

#endif // EXTENDED_EVALUATOR_HPP_
