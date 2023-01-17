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
    ~ExtendedEvaluator() override = default;

  private:
    Core::FOLContext ctx;
    Allocator<Core::Expr> epool;

    Tree* exprTree(Core::Expr const* e);
    Core::Expr const* treeExpr(Tree* e);
  };

}

#endif // EXTENDED_EVALUATOR_HPP_
