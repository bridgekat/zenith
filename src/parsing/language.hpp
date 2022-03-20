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


  // Specialize this for human-friendly type names (in debugging `Language`)
  // See: https://stackoverflow.com/questions/4484982/how-to-convert-typename-t-to-string-in-c
  template <typename T> struct SymbolName { static const string get() { return typeid(T).name(); } };
  // #define DEMANGLE_SYMBOL_NAME(T) template <> struct SymbolName<T> { static const char* get() { return #T; } };


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
  class Language: protected NFALexer, protected EarleyParser {
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
      bool discard; // Discard after scanning; for nonterminal symbols only
    };

    vector<Entry> symbols;
    unordered_map<std::type_index, Symbol> mp;
    Core::Allocator<ParseTree> pool;

    Language(): NFALexer(), EarleyParser(), symbols(), mp(), pool() {}

    // Get symbol index for type; insert new nonterminal symbol if not already present
    template <typename T>
    Symbol getSymbol() { return getSymbol(typeid(T)); }
    Symbol getSymbol(std::type_index tid);

    // Set as error symbol; can only be called at most once currently; do not add other rules to error symbols.
    template <typename T>
    void setAsErrorSymbol() { return setAsErrorSymbol(SymbolName<T>::get(), getSymbol<T>(), T{}); }
    void setAsErrorSymbol(const string& name, Symbol sym, std::any val);

    // Add a terminal symbol with a pattern.
    // `addPattern` (*) -> `addPatternImpl`
    template <typename T>
    Symbol addPattern(T action, NFA pattern, bool discard = false) {
      using U = LambdaConverter<T>;
      return addPatternImpl(
        SymbolName<typename U::ReturnType>::get(),
        typeid(typename U::ReturnType),
        pattern,
        discard,
        typename U::ConvertedType(action));
    }

    // Add a production rule. LHS must not be a known terminal symbol. Nonterminal symbols are automatically added.
    // `addRule` (*) -> `addRuleIndexed` (*) -> `addRuleImpl`
    template <typename T>
    Symbol addRule(T action) {
      using U = LambdaConverter<T>;
      return addRuleIndexed(
        SymbolName<typename U::ReturnType>::get(),
        typename U::ConvertedType(action),
        typename U::IndexSequence());
    }

    // Add a production rule with a more customized semantic action function that directly operates on the parse tree.
    // This could give more freedom on the order of evaluation, but the template arguments must be provided explicitly.
    // `addRuleFor` (*) -> `addRuleImpl`
    template <typename ReturnType, typename... ParamTypes>
    Symbol addRuleFor(std::function<ReturnType(const ParseTree*)> action) {
      return addRuleImpl(
        SymbolName<ReturnType>::get(),
        getSymbol<ReturnType>(),
        vector<Symbol>{ getSymbol<ParamTypes>()... },
        action);
    }

    // Execute semantic actions on a subtree. Used in raw actions.
    // Pre: type must be correct (will be checked)
    template <typename ReturnType>
    ReturnType get(const ParseTree* x) {
      std::type_index tid = typeid(ReturnType);
      auto it = mp.find(tid);
      if (it == mp.end()) throw Core::Unreachable("Language: unknown symbol");
      Symbol sym = it->second;
      if (x->id != sym) throw Core::Unreachable("Language: symbol mismatch");
      return std::any_cast<ReturnType>(symbols[sym].action(x));
    }

    // Execute semantic actions on a child node. Used in raw actions.
    // Pre: type and index must be correct (will be checked)
    template <typename ReturnType>
    ReturnType getChild(const ParseTree* x, size_t index) {
      x = x->c;
      for (size_t i = 0; i < index; i++) {
        if (!x) throw Core::Unreachable("Language: unexpected null pointer");
        x = x->s;
      }
      if (!x) throw Core::Unreachable("Language: unexpected null pointer");
      return get<ReturnType>(x);
    }

    // Parse with a given initial symbol (type).
    // `parse` (*) -> `parseImpl`
    template <typename ReturnType>
    std::optional<ReturnType> parse(const string& str) {
      std::type_index tid = typeid(ReturnType);
      auto it = mp.find(tid);
      if (it == mp.end()) throw Core::Unreachable("Language: unknown start symbol");
      Symbol start = it->second;
      ParseTree* x = parseImpl(str, start);
      if (!x) return std::nullopt;
      if (x->id != start) throw Core::Unreachable("Language: parsing completed with unexpected root node");
      return std::any_cast<ReturnType>(symbols[start].action(x));
    }

  private:

    // The "index trick" (pattern matching on index sequence)
    template <typename ReturnType, typename... ParamTypes, size_t... Indices>
    Symbol addRuleIndexed(const string& name, std::function<ReturnType(ParamTypes...)> action, std::index_sequence<Indices...>) {
      return addRuleImpl(
        name,
        getSymbol<ReturnType>(),
        vector<Symbol>{ getSymbol<ParamTypes>()... },
        [this, action] (const ParseTree* x) {
          vector<std::any> params;
          for (ParseTree* p = x->c; p; p = p->s) {
            params.push_back(symbols[p->id].action(p));
          }
          if (params.size() != sizeof...(ParamTypes)) throw Core::Unreachable("Langugage: arity does not match");
          return action(std::move(std::any_cast<typename std::decay<ParamTypes>::type>(params[Indices]))...);
        });
    }

    // Keep most of the code untemplated to avoid slowing down compilation
    Symbol addPatternImpl(const string& name, std::type_index tid, NFA pattern, bool discard, std::function<std::any(const string&)> action);
    Symbol addRuleImpl(const string& name, Symbol lhs, const vector<Symbol>& rhs, std::function<std::any(const ParseTree*)> action);
    ParseTree* parseImpl(const string& str, Symbol start);

  };

}

#endif // LANGUAGE_HPP_