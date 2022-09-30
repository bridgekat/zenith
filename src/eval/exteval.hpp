// Eval :: ExtendedEvaluator

#ifndef EXTEVAL_HPP_
#define EXTEVAL_HPP_

#include <core.hpp>
#include "evaluator.hpp"

namespace Eval {

  class ExtendedEvaluator: public Evaluator {
  public:
    ExtendedEvaluator();
    ~ExtendedEvaluator() override = default;

  private:
    Core::FOLContext ctx;
    Core::Allocator<Core::Expr> epool;

    Tree* exprTree(Core::Expr const* e);
    Core::Expr const* treeExpr(Tree* e);
  };

}

#endif // EXTEVAL_HPP_
