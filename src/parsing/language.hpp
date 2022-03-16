// Parsing :: Language

#ifndef LANGUAGE_HPP_
#define LANGUAGE_HPP_

#include <typeinfo>
#include <typeindex>
#include <utility>
#include <functional>
#include <any>
#include <type_traits>
#include "parser.hpp"


namespace Parsing {

  using std::string;
  using std::vector;
  using std::unordered_map;


  // Specialize this for human-friendly type names (in debugging `Language`)
  // See: https://stackoverflow.com/questions/4484982/how-to-convert-typename-t-to-string-in-c
  template <typename T> struct SymbolName { static const char* get() { return typeid(T).name(); } };
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

  class Language: protected NFALexer, protected EarleyParser {
  public:
    struct Entry {
      string name;
      std::function<std::any(const ParseTree*)> action;
      bool discard; // Discard after scanning
    };
    vector<Entry> symbols;
    unordered_map<std::type_index, Symbol> mp;

    Language(): NFALexer(), EarleyParser(), symbols(), mp() {}

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

    template <typename T>
    Symbol addRule(T action) {
      using U = LambdaConverter<T>;
      return addRuleIndexed(
        SymbolName<typename U::ReturnType>::get(),
        typename U::ConvertedType(action),
        typename U::IndexSequence());
    }

    template <typename ReturnType>
    ReturnType parse(const string& str) {
      std::type_index tid = typeid(ReturnType);
      auto it = mp.find(tid);
      if (it == mp.end()) throw Core::NotImplemented("Language: unknown start symbol");
      Symbol start = it->second;
      ParseTree* x = parseImpl(str, start);
      return std::any_cast<ReturnType>(symbols[start].action(x));
    }

  private:

    template <typename ReturnType, typename... ParamTypes, size_t... Indices>
    Symbol addRuleIndexed(const string& name, std::function<ReturnType(ParamTypes...)> action, std::index_sequence<Indices...>) {
      return addRuleImpl(
        name,
        typeid(ReturnType),
        vector<std::type_index>{ typeid(ParamTypes)... },
        [action] (const vector<std::any>& params) {
          if (params.size() != sizeof...(ParamTypes)) throw Core::Unreachable("Langugage: arity does not match");
          return action(std::any_cast<typename std::decay<ParamTypes>::type>(params[Indices])...);
        });
    }

    Symbol addPatternImpl(const string& name, std::type_index tid, NFA pattern, bool discard, std::function<std::any(const string&)> action);
    Symbol addRuleImpl(const string& name, std::type_index tid, const vector<std::type_index>& rhstid, std::function<std::any(const vector<std::any>&)> action);
    ParseTree* parseImpl(const string& str, Symbol start);

  };

}

#endif // LANGUAGE_HPP_
