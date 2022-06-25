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
    Core::Context ctx;
    Core::Allocator<Core::Expr> epool;

    Tree* exprTree(const Core::Expr* e);
    const Core::Expr* treeExpr(Tree* e);
  };

}

#endif // EXTEVAL_HPP_
