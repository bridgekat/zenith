// Eval :: EvalError, Evaluator...

#ifndef EVALUATOR_HPP_
#define EVALUATOR_HPP_

#include <functional>
#include <initializer_list>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>
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
    const Tree *at, *e;
    EvalError(const std::string& s, const Tree* at, const Tree* e): std::runtime_error(s), at(at), e(e) {}
    EvalError(const EvalError&) = default;
    EvalError& operator=(const EvalError&) = default;
  };

  // Throw this to let the most recent call of `Evaluator::eval()` to provide context.
  struct PartialEvalError: public EvalError {
    PartialEvalError(const std::string& s, const Tree* at): EvalError(s, at, at) {}
  };

  // Convenient pattern-matching functions (throw customized exceptions on failure)
  template <typename T>
  inline T& expect(Tree*) {
    unreachable;
  }

#define defineExpect(T, msg)                                                                          \
  template <>                                                                                         \
  inline T& expect<T>(Tree * e) {                                                                     \
    try {                                                                                             \
      return std::get<T>(e->v);                                                                       \
    } catch (std::bad_variant_access&) { throw PartialEvalError((msg ", got ") + e->toString(), e); } \
  }
  defineExpect(Nil, "expected end-of-list")
  defineExpect(Cons, "expected non-empty list")
  defineExpect(Symbol, "expected symbol")
  defineExpect(Nat64, "expected number")
  defineExpect(String, "expected string")
  defineExpect(Bool, "expected boolean")
  defineExpect(Closure, "expected function")
  defineExpect(Native, "expected native type")
#undef defineExpect

  template <typename T>
  inline T expectNative(Tree* e) {
    try {
      return std::any_cast<T>(expect<Native>(e).val);
    } catch (std::bad_any_cast& ex) { throw PartialEvalError(std::string("native type mismatch: ") + ex.what(), e); }
  }

  // The main interpreter (evaluator) class.
  // Turns strings into parse `Tree`s, then expand macros, then evaluate and gives a resulting `Tree`.
  // Also stores all states that can be "side-effected" by evaluation.
  class Evaluator {
  public:
    Evaluator();
    Evaluator(const Evaluator&) = delete;
    Evaluator& operator=(const Evaluator&) = delete;
    virtual ~Evaluator() = default;

    // Set the string of statements to be evaluated.
    void setString(const std::string& s) { lexer.setString(s); }

    // Parses next statement (results will be stored).
    bool parseNextStatement();

    // Evaluates parsed statement and returns result.
    // This will store intermediate and final results on `this.pool`.
    Tree* evalParsedStatement();

    // Returns and clears error log
    std::vector<ParsingError> popParsingErrors();

  protected:
    // `env != nullptr` means that `e` still needs to be evaluated under `env` (for proper tail recursion).
    struct Result {
      Tree *env, *e;
      Result(Tree* e): env(nullptr), e(e){};
      Result(Tree* env, Tree* e): env(env), e(e){};
    };
    using PrimitiveFunc = std::pair<bool, std::function<Result(Tree*, Tree*)>>;
    static constexpr Parsing::Symbol IgnoredSymbol = 0;
    static constexpr Parsing::Symbol StartSymbol = 1;

    Core::Allocator<Tree> pool;
    Eval::Tree *nil, *unit;

    Eval::Tree *patterns, *rules;
    std::vector<std::string> symbolNames;
    std::unordered_map<std::string, Parsing::Symbol> nameSymbols;
    std::vector<std::string> patternNames, ruleNames;
    Parsing::NFALexer lexer;
    Parsing::EarleyParser parser;

    Eval::Tree* globalEnv;
    std::vector<Closure> macros;
    std::unordered_map<std::string, size_t> nameMacros;
    std::vector<PrimitiveFunc> prims;
    std::unordered_map<std::string, size_t> namePrims;

    size_t getSymbol(const std::string& name) {
      const auto it = nameSymbols.find(name);
      if (it != nameSymbols.end()) return it->second;
      size_t id = symbolNames.size();
      symbolNames.push_back(name);
      nameSymbols[name] = id;
      return id;
    }

    Parsing::NFALexer::NFA treePattern(Tree* e);
    std::vector<Parsing::NFALexer::NFA> listPatterns(Tree* e);
    std::vector<std::pair<Parsing::Symbol, Parsing::Prec>> listSymbols(Tree* e);
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
    Tree* resolve(size_t maxDepth = 4096);
    Tree* expand(Tree* e);
    Tree* expandList(Tree* e);
    Tree* eval(Tree* env, Tree* e);
    Tree* evalList(Tree* env, Tree* e);
    Tree* beginList(Tree* env, Tree* e);
    Tree* quasiquote(Tree* env, Tree* e);
  };

}

#endif // EVALUATOR_HPP_
