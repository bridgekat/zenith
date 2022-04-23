// Parsing :: Language

#ifndef LANGUAGE_HPP_
#define LANGUAGE_HPP_

#include <typeinfo>
#include <typeindex>
#include <utility>
#include <functional>
#include <any>
#include <type_traits>
#include <optional>
#include "parser.hpp"


namespace Parsing {

  using std::string;
  using std::vector;
  using std::unordered_map;


  // Lexer + parser + pretty-printer in one place, with variadic templates and other C++ magics.
  // It uses types to index (terminal and nonterminal) symbols, and uses function signatures as production rules;
  // The functions themselves serve as semantic actions.
  // See: https://devblogs.microsoft.com/cppblog/stdany-how-when-and-why/
  // See: https://en.cppreference.com/w/cpp/language/parameter_pack
  // See: https://github.com/jsonrpcx/json-rpc-cxx/blob/master/include/jsonrpccxx/typemapper.hpp
  // See: https://stackoverflow.com/questions/7943525/is-it-possible-to-figure-out-the-parameter-type-and-return-type-of-a-lambda

  // For generic types, directly use the result of the signature of its 'operator()'
  template <typename T>
  struct LambdaConverter: public LambdaConverter<decltype(&T::operator())> {};

  // We specialize for pointers to member function
  template <typename ClassType, typename ReturnType_, typename... ParamTypes>
  struct LambdaConverter<ReturnType_(ClassType::*)(ParamTypes...) const> {
    using ConvertedType = std::function<ReturnType_(ParamTypes...)>;
    using ReturnType = ReturnType_;
    using IndexSequence = std::index_sequence_for<ParamTypes...>;
  };

  // Inherit from this class to create new languages.
  class Language {
  public:
    struct ParsingErrorException: public std::runtime_error {
      size_t startPos, endPos;
      ParsingErrorException(size_t startPos, size_t endPos, const string& s):
        std::runtime_error(s), startPos(startPos), endPos(endPos) {}
    };

    vector<ParsingErrorException> popParsingErrors();

  protected:
    struct Entry {
      string name;
      std::function<std::any(const ParseTree*)> action;
    };

    vector<Entry> symbols;
    unordered_map<std::type_index, Symbol> mp;
    Core::Allocator<ParseTree> pool;

    NFALexer lexer;
    EarleyParser parser;

    Language(): symbols(), mp(), pool(), lexer(), parser(lexer) {}

    // Get symbol index for type; insert new nonterminal symbol if not already present
    template <typename T>
    Symbol getSymbol() { return getSymbol(typeid(T)); }
    Symbol getSymbol(std::type_index tid);

    // Dynamically generate a new symbol ID, distinct from all known symbols
    Symbol newSymbol(const string& name = "");

    // Set as ignored symbol; can only be called at most once currently.
    template <typename T>
    void setAsIgnoredSymbol() { return setAsIgnoredSymbol(typeid(T).name(), getSymbol<T>()); }
    void setAsIgnoredSymbol(const string& name, Symbol sym);

    // Add pattern for terminal symbol.
    // `addPattern` (*) -> `addPatternImpl`
    template <typename T>
    size_t addPattern(T action, NFALexer::NFA pattern) {
      using U = LambdaConverter<T>;
      return addPatternImpl(
        typeid(typename U::ReturnType).name(),
        getSymbol<typename U::ReturnType>(),
        pattern,
        [action] (const ParseTree* x) { return action(x->lexeme.value()); });
    }

    // Add a production rule. Symbols on the RHS are automatically added.
    // `addRule` (*) -> `addRuleIndexed` (*) -> `addRuleImpl`
    template <typename T>
    size_t addRule(T action, size_t prec = 0) {
      using U = LambdaConverter<T>;
      return addRuleIndexed(
        typeid(typename U::ReturnType).name(),
        typename U::ConvertedType(action),
        typename U::IndexSequence(),
        prec);
    }

    // Add a production rule with a more customized semantic action function that directly operates on the parse tree.
    // This could give more freedom on the order of evaluation, but the template arguments must be provided explicitly.
    // `addRuleFor` (*) -> `addRuleImpl`
    template <typename ReturnType, typename... ParamTypes>
    size_t addRuleFor(std::function<ReturnType(const ParseTree*)> action, size_t prec = 0) {
      return addRuleImpl(
        typeid(ReturnType).name(),
        getSymbol<ReturnType>(),
        vector<Symbol>{ getSymbol<ParamTypes>()... },
        action,
        prec);
    }

    // Execute semantic actions on a subtree. Used in raw actions.
    // Pre: type must be correct (will be checked)
    template <typename ReturnType>
    ReturnType get(const ParseTree* x) {
      std::type_index tid = typeid(ReturnType);
      auto it = mp.find(tid);
      if (it == mp.end()) unreachable;
      Symbol sym = it->second;
      if (x->id != sym) unreachable;
      return std::any_cast<ReturnType>(symbols[sym].action(x));
    }

    // Execute semantic actions on a child node. Used in raw actions.
    // Pre: type and index must be correct (will be checked)
    template <typename ReturnType>
    ReturnType getChild(const ParseTree* x, size_t index) {
      x = x->c;
      for (size_t i = 0; i < index; i++) {
        if (!x) unreachable;
        x = x->s;
      }
      if (!x) unreachable;
      return get<ReturnType>(x);
    }

    // Parse next sentence with a given initial symbol (type).
    // `nextSentence` (*) -> `nextSentenceImpl`
    template <typename ReturnType>
    std::optional<ReturnType> nextSentence() {
      std::type_index tid = typeid(ReturnType);
      auto it = mp.find(tid);
      if (it == mp.end()) unreachable;
      Symbol start = it->second;
      ParseTree* x = nextSentenceImpl(start);
      if (!x) return std::nullopt;
      if (x->id != start) unreachable;
      return std::any_cast<ReturnType>(symbols[start].action(x));
    }

    // Keep more code untemplated to avoid slowing down compilation
    size_t addPatternImpl(const string& name, Symbol sym, NFALexer::NFA pattern, std::function<std::any(const ParseTree*)> action);
    size_t addRuleImpl(const string& name, Symbol lhs, const vector<Symbol>& rhs, std::function<std::any(const ParseTree*)> action, size_t prec = 0);
    ParseTree* nextSentenceImpl(Symbol start);

  private:

    // The "index trick" (pattern matching on index sequence)
    template <typename ReturnType, typename... ParamTypes, size_t... Indices>
    size_t addRuleIndexed(const string& name, std::function<ReturnType(ParamTypes...)> action, std::index_sequence<Indices...>, size_t prec = 0) {
      return addRuleImpl(
        name,
        getSymbol<ReturnType>(),
        vector<Symbol>{ getSymbol<ParamTypes>()... },
        [this, action] (const ParseTree* x) {
          vector<std::any> params;
          for (ParseTree* p = x->c; p; p = p->s) params.push_back(symbols[p->id].action(p));
          if (params.size() != sizeof...(ParamTypes)) unreachable;
          return action(std::move(std::any_cast<typename std::decay<ParamTypes>::type>(params[Indices]))...);
        },
        prec);
    }

  };

}

#endif // LANGUAGE_HPP_
