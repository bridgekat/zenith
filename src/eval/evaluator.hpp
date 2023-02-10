#ifndef APIMU_EVAL_EVALUATOR_HPP
#define APIMU_EVAL_EVALUATOR_HPP

#include <functional>
#include <initializer_list>
#include <memory>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>
#include <parsing/lexer.hpp>
#include <parsing/parser.hpp>
#include "parsing/stream.hpp"
#include "tree.hpp"

namespace apimu::eval {
#include "macros_open.hpp"

  // parsing error exception.
  struct ParsingError: public std::runtime_error {
    size_t begin;
    size_t end;

    ParsingError(std::string const& s, size_t begin, size_t end):
      std::runtime_error(s),
      begin(begin),
      end(end) {}
  };

  // Evaluation error exception.
  struct EvalError: public std::runtime_error {
    Tree const* at;
    Tree const* e;

    EvalError(std::string const& s, Tree const* at, Tree const* e):
      std::runtime_error(s),
      at(at),
      e(e) {}
  };

  // Throw this to let the most recent call of `Evaluator::eval()` to provide context.
  struct PartialEvalError: public EvalError {
    PartialEvalError(std::string const& s, Tree const* at):
      EvalError(s, at, at) {}
  };

  // Convenient pattern-matching functions (throw customized exceptions on failure).
  template <typename T>
  inline auto expect(Tree*) -> T& {
    unreachable;
  }

#define defineExpect(T, msg)                                                                          \
  template <>                                                                                         \
  inline auto expect<T>(Tree * e)->T& {                                                               \
    try {                                                                                             \
      return std::get<T>(*e);                                                                         \
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
  inline auto expectNative(Tree* e) -> T {
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
    Evaluator(Evaluator const&) = delete;
    Evaluator(Evaluator&&) = delete;
    auto operator=(Evaluator const&) -> Evaluator& = delete;
    auto operator=(Evaluator&&) -> Evaluator& = delete;
    virtual ~Evaluator() = default;

    auto setString(std::string const& s) -> void {
      assert(automaton && grammar);
      stream = std::make_unique<parsing::CharStream>(s);
      parser = std::make_unique<Parser>(*automaton, *grammar, *stream);
    }

    // Parses next statement (results will be stored).
    auto parseNextStatement() -> bool;

    // Evaluates parsed statement and returns result.
    // This will store intermediate and final results on `this.pool`.
    auto evalParsedStatement() -> Tree*;

    // Returns and clears error log.
    auto parsingErrors() -> std::vector<ParsingError>;

  protected:
    struct Parser {
      static constexpr auto defaultParams = parsing::ErrorRecoveryParams{
        .rollback = true,
        .maxSkipped = 5,
        .threshold = 5,
      };

      parsing::AutomatonLexer lexer;
      parsing::BufferedStream<parsing::Token> buffer;
      parsing::EarleyParser parser;
      parsing::BasicErrorHandler handler;

      Parser(parsing::Automaton const& automaton, parsing::Grammar const& grammar, parsing::CharStream& stream):
        lexer(automaton, stream),
        buffer(lexer),
        parser(grammar, buffer, defaultParams, handler) {}
    };

    // `env != nullptr` means that `e` still needs to be evaluated under `env` (for proper tail recursion).
    struct Result {
      Tree* env;
      Tree* e;

      Result(Tree* e):
        env(nullptr),
        e(e){};
      Result(Tree* env, Tree* e):
        env(env),
        e(e){};
    };
    using PrimitiveFunc = std::pair<bool, std::function<Result(Tree*, Tree*)>>;

    static constexpr parsing::Symbol ignoredSymbol = 0;
    static constexpr parsing::Symbol startSymbol = 1;
    static constexpr size_t defaultMaxDepth = 4096;

    auto pool() -> Allocator<Tree>& { return _pool; }
    auto nil() -> eval::Tree* { return _nil; }
    auto unit() -> eval::Tree* { return _unit; }

    auto makeList(std::initializer_list<Tree*> const& es) -> Tree* {
      auto res = nil();
      for (auto it = std::rbegin(es); it != std::rend(es); it++) res = pool().make(*it, res);
      return res;
    }

    auto symbol(bool isTerminal, std::string const& name) -> parsing::Symbol {
      if (auto const it = nameSymbols.find(name); it != nameSymbols.end())
        return static_cast<parsing::Symbol>(it->second);
      auto const id = symbolIsTerminal.size();
      symbolIsTerminal.push_back(isTerminal);
      symbolNames.push_back(name);
      nameSymbols[name] = id;
      return static_cast<parsing::Symbol>(id);
    }

    auto treePattern(parsing::AutomatonBuilder& builder, Tree* e) -> parsing::AutomatonBuilder::Subgraph;
    auto listPatterns(parsing::AutomatonBuilder& builder, Tree* e) -> std::vector<parsing::AutomatonBuilder::Subgraph>;
    auto listSymbols(Tree* e) -> std::vector<parsing::GrammarBuilder::InputPair>;
    auto setSyntax(Tree* p, Tree* r) -> void;

    auto addMacro(std::string const& name, Closure const& cl) -> size_t {
      auto const id = macros.size();
      macros.push_back(cl);
      nameMacros[name] = id;
      return id;
    }

    auto addPrimitive(std::string const& name, bool evalParams, std::function<Result(Tree*, Tree*)> const& f)
      -> size_t {
      auto const id = prims.size();
      prims.emplace_back(evalParams, f);
      namePrims[name] = id;
      return id;
    }

    auto treeMatch(Tree* e, Tree* pat, Tree*& env, bool quoteMode = false) -> bool;

    // Far less efficient than hash tries (HAMTs), but should be enough for current purpose!
    auto extend(Tree* env, std::string const& sym, Tree* e) -> Tree*;
    auto lookup(Tree* env, std::string const& sym) -> Tree*;

    auto resolve(parsing::Node const& node, std::vector<Tree*> const& tails, size_t maxDepth) -> std::vector<Tree*>;
    auto resolve(size_t maxDepth = defaultMaxDepth) -> Tree*;
    auto expand(Tree* e) -> Tree*;
    auto expandList(Tree* e) -> Tree*;
    auto eval(Tree* env, Tree* e) -> Tree*;
    auto evalList(Tree* env, Tree* e) -> Tree*;
    auto beginList(Tree* env, Tree* e) -> Tree*;
    auto quasiquote(Tree* env, Tree* e) -> Tree*;

  private:
    Allocator<Tree> _pool;
    eval::Tree* _nil = _pool.make(Nil{});
    eval::Tree* _unit = _pool.make(Unit{});

    eval::Tree* patterns = nil();
    eval::Tree* rules = nil();
    eval::Tree* globalEnv = nil();

    std::unique_ptr<parsing::Automaton const> automaton;
    std::unique_ptr<parsing::Grammar const> grammar;
    std::unique_ptr<parsing::CharStream> stream;
    std::unique_ptr<Parser> parser;

    std::vector<bool> symbolIsTerminal;
    std::vector<std::string> symbolNames;
    std::unordered_map<std::string, size_t> nameSymbols;
    std::vector<std::string> ruleNames;
    std::unordered_map<std::string, size_t> nameRules;

    std::vector<Closure> macros;
    std::unordered_map<std::string, size_t> nameMacros;
    std::vector<PrimitiveFunc> prims;
    std::unordered_map<std::string, size_t> namePrims;
  };

#include "macros_close.hpp"
}

#endif // APIMU_EVAL_EVALUATOR_HPP
