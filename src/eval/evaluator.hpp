// Eval :: EvalError, Evaluator...

#ifndef EVALUATOR_HPP_
#define EVALUATOR_HPP_

#include <string>
#include <vector>
#include <unordered_map>
#include <utility>
#include <functional>
#include <initializer_list>
#include <core.hpp>
#include <parsing/lexer.hpp>
#include <parsing/parser.hpp>
#include "tree.hpp"


namespace Eval {

  // Parsing error exception
  struct ParsingError: public std::runtime_error {
    size_t startPos, endPos;
    ParsingError(const std::string& s, size_t startPos, size_t endPos):
      std::runtime_error(s), startPos(startPos), endPos(endPos) {}
  };

  // Evaluation error exception
  struct EvalError: public std::runtime_error {
    const Tree* at, * e;
    EvalError(const std::string& s, const Tree* at, const Tree* e):
      std::runtime_error(s), at(at), e(e) {}
    EvalError(const EvalError&) = default;
    EvalError& operator=(const EvalError&) = default;
  };

  // The main interpreter (evaluator) class.
  // Turns strings into parse `Tree`s, then expand macros, then evaluate and gives a resulting `Tree`.
  // Also maintains all states that can be "side-effected" by evaluation.
  class Evaluator {
  public:
    Evaluator();
    Evaluator(const Evaluator&) = delete;
    Evaluator& operator=(const Evaluator&) = delete;
    ~Evaluator() = default;

    // Set the string of statements to be evaluated.
    void setString(const std::string& s) { lexer.setString(s); }

    // Evaluates next statement, returns result, or `nullptr` on reaching EOF.
    // This will store intermediate and final results on `this.pool`.
    Tree* evalNextStatement();

    // Returns and clears error log
    std::vector<ParsingError> popParsingErrors();

  protected:
    // `env != nullptr` means that `e` still needs to be evaluated under `env` (for proper tail recursion).
    struct Result {
      Tree* env, * e;
      Result(Tree* e): env(nullptr), e(e) {};
      Result(Tree* env, Tree* e): env(env), e(e) {};
    };
    using PrimitiveFunc = std::pair<bool, std::function<Result(Tree*, Tree*)>>;
    static constexpr Parsing::Symbol IgnoredSyncat = 0;
    static constexpr Parsing::Symbol StartSyncat = 1;

    Core::Allocator<Tree> pool;
    Eval::Tree* nil, * unit;

    Eval::Tree* patterns, * rules;
    std::vector<std::string> syncatNames;
    std::unordered_map<std::string, Parsing::Symbol> nameSyncats;
    std::vector<std::string> patternNames, ruleNames;
    Parsing::NFALexer lexer;
    Parsing::EarleyParser parser;

    Eval::Tree* globalEnv;
    std::vector<Closure> macros;
    std::unordered_map<std::string, size_t> nameMacros;
    std::vector<PrimitiveFunc> prims;
    std::unordered_map<std::string, size_t> namePrims;

    size_t getSyncat(const std::string& name) {
      const auto it = nameSyncats.find(name);
      if (it != nameSyncats.end()) return it->second;
      size_t id = syncatNames.size();
      syncatNames.push_back(name);
      nameSyncats[name] = id;
      return id;
    }

    Parsing::NFALexer::NFA treePattern(Tree* e);
    std::vector<Parsing::NFALexer::NFA> listPatterns(Tree* e);
    std::vector<std::pair<Parsing::Symbol, Parsing::Prec>> listSyncats(Tree* e);
    void setSyntax(Tree* p, Tree* r);
    Tree* makeList(const std::initializer_list<Tree*>& es);

    size_t addMacro(const std::string& name, const Closure& cl) {
      size_t id = macros.size();
      macros.push_back(cl);
      nameMacros[name] = id;
      return id;
    }

    size_t addPrimitive(const std::string& name, const PrimitiveFunc& f) {
      size_t id = prims.size();
      prims.push_back(f);
      namePrims[name] = id;
      return id;
    }

    bool match(Tree* e, Tree* pat, Tree*& env, bool quoteMode = false);

    // Far less efficient than hash tries (HAMTs), but should be enough for current purpose!
    Tree* extend(Tree* env, const std::string& sym, Tree* e);
    Tree* lookup(Tree* env, const std::string& sym);

    std::vector<Tree*> resolve(Parsing::EarleyParser::Location loc, const std::vector<Tree*>& right, size_t maxDepth);
    Tree* resolve(size_t maxDepth = 64);
    Tree* expand(Tree* e);
    Tree* expandList(Tree* e);
    Tree* eval(Tree* env, Tree* e);
    Tree* evalList(Tree* env, Tree* e);
    Tree* beginList(Tree* env, Tree* e);
    Tree* quasiquote(Tree* env, Tree* e);
  };

}

#endif // EVALUATOR_HPP_
