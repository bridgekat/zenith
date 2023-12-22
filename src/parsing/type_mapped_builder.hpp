#ifndef APIMU_PARSING_TYPE_MAPPED_BUILDER_HPP
#define APIMU_PARSING_TYPE_MAPPED_BUILDER_HPP

#include <initializer_list>
#include <tuple>
#include <typeindex>
#include "type_erased_visitor.hpp"

namespace apimu::parsing {
#include "macros_open.hpp"

  // Type "decorators".
  template <typename T, Precedence P>
  struct WithPrecedence: T {
    WithPrecedence(T value):
        T(value) {}
  };

  namespace detail {
    // Helper templates.
    template <typename T>
    struct SymbolTypeTraits {
      using Base = std::remove_cvref_t<T>;
      static constexpr Precedence Prec = PrecedenceMax;
    };
    template <typename T, Precedence P>
    struct SymbolTypeTraits<WithPrecedence<T, P>>: SymbolTypeTraits<T> {
      static constexpr Precedence Prec = P;
    };

    // https://stackoverflow.com/questions/7943525/is-it-possible-to-figure-out-the-parameter-type-and-return-type-of-a-lambda
    // Modified to use first argument as returning reference.
    template <typename F>
    struct ClosureTraits: ClosureTraits<decltype(&F::operator())> {};
    template <typename ClosureType, typename T, typename... Ts>
    struct ClosureTraits<void (ClosureType::*)(T, Ts...) const> {
      using RetDecr = T;
      using Ret = typename SymbolTypeTraits<RetDecr>::Base;
      template <size_t I>
      using ArgDecr = std::tuple_element_t<I, std::tuple<Ts...>>;
      template <size_t I>
      using Arg = typename SymbolTypeTraits<ArgDecr<I>>::Base;
      using Indices = std::index_sequence_for<Ts...>;
    };
  }

  // Experimental.
  template <typename Context>
  class TypeMappedBuilder: public AutomatonBuilder, public GrammarBuilder {
  public:
    template <typename T>
    using View = typename TypeErasedVisitor<Context>::template View<T>;
    using Handle = typename TypeErasedVisitor<Context>::Handle;

    // Maps an optionally "decorated" type to `Parsing::Symbol`.
    // Inserts new entry if not already exists.
    template <typename T>
    auto map() -> Symbol {
      return _map<T>().value.first;
    }

    template <typename T>
    auto name(std::string name) -> TypeMappedBuilder& {
      _names[map<T>()] = std::move(name);
      return *this;
    }

    auto name(std::string name) -> TypeMappedBuilder& {
      _names[_last.value()] = std::move(name);
      return *this;
    }

    template <typename T>
    auto ignored() -> TypeMappedBuilder& {
      GrammarBuilder::ignored(map<T>());
      return *this;
    }

    template <typename T>
    auto start() -> TypeMappedBuilder& {
      GrammarBuilder::start(map<T>());
      return *this;
    }

    template <typename T>
    auto pattern(Subgraph g) -> TypeMappedBuilder& {
      _pattern(map<T>(), g);
      return *this;
    }

    auto pattern(Subgraph g) -> TypeMappedBuilder& {
      _pattern(_last.value(), g);
      return *this;
    }

    template <typename F>
    auto rule(F&& f) -> TypeMappedBuilder& {
      using T = detail::ClosureTraits<F>;
      _rule(std::forward<F>(f), typename T::Indices());
      return *this;
    }

    auto numSymbols() const -> Symbol {
      return static_cast<Symbol>(_patternHandlers.size());
    }
    auto mapped() const -> auto const& {
      return _mapped;
    }
    auto names() const -> auto const& {
      return _names;
    }
    auto patternHandlers() const -> auto const& {
      return _patternHandlers;
    }
    auto ruleHandlers() const -> auto const& {
      return _ruleHandlers;
    }

  private:
    std::optional<Symbol> _last;
    std::unordered_map<std::type_index, Symbol> _mapped;
    std::vector<std::optional<std::string>> _names;
    std::vector<std::function<void(Handle&, std::string_view)>> _patternHandlers;
    std::vector<std::function<void(Handle&, std::span<Handle>)>> _ruleHandlers;

    // Maps an optionally "decorated" type to `Parsing::GrammarBuilder::InputPair`.
    // Inserts new entry if not already exists.
    template <typename T>
    auto _map() -> InputPair {
      auto const sym = _map(typeid(typename detail::SymbolTypeTraits<T>::Base));
      auto const prec = detail::SymbolTypeTraits<T>::Prec;
      _last = sym;
      return {sym, prec};
    }

    // Maps an `std::type_index` to `Parsing::Symbol`.
    auto _map(std::type_index tid) -> Symbol {
      if (auto const it = _mapped.find(tid); it != _mapped.end())
        return it->second;
      auto const id = _names.size();
      _names.emplace_back();
      _patternHandlers.emplace_back();
      return _mapped[tid] = static_cast<Symbol>(id);
    }

    auto _pattern(Symbol sym, Subgraph g) -> void {
      _patternHandlers[sym] = [](Handle& out, std::string_view sv) {
        View<std::string_view>(out) << sv;
      };
      AutomatonBuilder::pattern(sym, g);
    }

    // The "index trick": http://loungecpp.wikidot.com/tips-and-tricks:indices
    template <typename F, size_t... Is>
    auto _rule(F&& f, std::index_sequence<Is...>) -> void {
      using T = detail::ClosureTraits<F>;
      _ruleHandlers.emplace_back([f](Handle& out, [[maybe_unused]] std::span<Handle> hs) {
        // Assuming base types can be aggregate-initialised from `Handle&`.
        // Assuming base types can be implicitly converted to "decorated" types.
        f(typename T::Ret{out}, typename T::template Arg<Is>{hs[Is]}...);
      });
      GrammarBuilder::rule(_map<typename T::RetDecr>(), {_map<typename T::template ArgDecr<Is>>()...});
    }
  };

#include "macros_close.hpp"
}

#endif // APIMU_PARSING_TYPE_MAPPED_BUILDER_HPP
