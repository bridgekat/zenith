// Eval :: EvalError, Evaluator...

#ifndef EVALUATOR_HPP_
#define EVALUATOR_HPP_

#include <string>
#include <vector>
#include <unordered_map>
#include <utility>
#include <functional>
#include <core.hpp>
#include <parsing/lexer.hpp>
#include <parsing/parser.hpp>
#include "tree.hpp"


namespace Eval {

  struct EvalError: public std::runtime_error {
    const Tree* at, * e;
    EvalError(const std::string& s, const Tree* at, const Tree* e): std::runtime_error(s), at(at), e(e) {}
    EvalError(const EvalError&) = default;
    EvalError& operator=(const EvalError&) = default;
  };

  // The main interpreter (evaluator) class.
  // Turns strings into parse `Tree`s, then expand macros, then evaluate and gives a resulting `Tree`.
  // Also maintains all states that can be side-effected by evaluation.
  class Evaluator {
  public:
    Evaluator();
    Evaluator(Evaluator&&) = default;
    Evaluator& operator=(Evaluator&&) = default;
    ~Evaluator() = default;

    // Set the string of statements to be evaluated.
    void setString(const string& s) { lexer.setString(s); }

    // Evaluates next statement, returns result, or `nullptr` on reaching EOF.
    // This will store intermediate and final results on `this.pool`.
    Tree* evalNextStatement();

  private:
    // `env != nullptr` means that `e` still needs to be evaluated under `env` (for proper tail recursion).
    struct Result {
      Tree* env, * e;
      Result(Tree* e): env(nullptr), e(e) {};
      Result(Tree* env, Tree* e): env(env), e(e) {};
    };
    using PrimitiveFunc = std::function<Result(Tree*, Tree*)>;

    std::vector<std::pair<bool, PrimitiveFunc>> prims;
    std::unordered_map<std::string, size_t> primNames;
    Core::Allocator<Tree> pool;
    Eval::Tree* globalEnv, * nil, * unit;
    Parsing::NFALexer lexer;
    Parsing::EarleyParser parser;

    size_t addPrim(bool evalParams, PrimitiveFunc f) {
      size_t res = prims.size();
      prims.emplace_back(evalParams, f);
      return res;
    }

    std::vector<Tree*> resolveParse(Parsing::EarleyParser::Location loc, size_t numResults = 64, size_t maxDepth = 4096) const;
    bool match(Tree* e, Tree* pat, Tree*& env, bool quoteMode = false);

    // Far less efficient than hash tries (HAMTs), but should be enough for current purpose!
    Tree* extend(Tree* env, const std::string& sym, Tree* e);
    Tree* lookup(Tree* env, const std::string& sym);

    Tree* eval(Tree* env, Tree* e);
    Tree* evalList(Tree* env, Tree* e);
    Tree* evalListExceptLast(Tree* env, Tree* e);
    Tree* evalQuasiquote(Tree* env, Tree* e);
  };

  /*
  // Build an S-expression representation of a logical expression (lifetime bounded by `pool`).
  Tree* ExprTree(const Core::Expr* e, Core::Allocator<Tree>& pool);

  // Try convert S-expression to logical expression (lifetime bounded by `pool`).
  // Throws `EvalError` if not well-formed.
  const Core::Expr* TreeExpr(Tree* e, Core::Allocator<Core::Expr>& pool);
  */

}

#endif // EVALUATOR_HPP_
