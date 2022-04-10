// Eval :: Matcher, SExpr, Nil, Cons, VarType...

#ifndef SEXPR_HPP_
#define SEXPR_HPP_

#include <cstdint>
#include <string>
#include <variant>
#include <utility>
#include <core/base.hpp>


namespace Eval {

  // See: https://en.cppreference.com/w/cpp/utility/variant/visit
  template <typename... Ts> struct Matcher: Ts... { using Ts::operator()...; };

  // A generic representation for different tree structures.
  // Intended for use as an exchange / transformation format.
  // `T` must be the variant type itself or some derived class;
  // `Ts...` denote all possible types of an atom.
  // (C++23 will allow direct visitation on classes derived from `std::variant`...)
  template <typename T, typename... Ts> struct BasicSExpr;
  template <typename T, typename... Ts> struct BasicNil {};
  template <typename T, typename... Ts> struct BasicCons { const T* head{}, * tail{}; };
  template <typename T, typename... Ts> struct BasicSExpr { std::variant<BasicNil<T, Ts...>, BasicCons<T, Ts...>, Ts...> v{}; };

  // Concrete atom types for SExpr
  struct Symbol { std::string s; };
  using Number = int32_t;
  using String = std::string;
  using Boolean = bool;
  using Undefined = std::monostate;

  // Main SExpr type
  class SExpr;
  using Nil = BasicNil<SExpr, Symbol, Number, String, Boolean, Undefined>;
  using Cons = BasicCons<SExpr, Symbol, Number, String, Boolean, Undefined>;
  using VarType = BasicSExpr<SExpr, Symbol, Number, String, Boolean, Undefined>;

  class SExpr: public VarType {
  public:
    // Convenient constructors
    SExpr(): VarType{} {}
    SExpr(const SExpr* l, const SExpr* r): VarType{ Cons{ l, r } } {}
    SExpr(Nil): VarType{} {}
    SExpr(Cons const& cons): VarType{ cons } {}
    SExpr(Symbol const& sym): VarType{ sym } {}
    SExpr(Number const& num): VarType{ num } {}
    SExpr(String const& str): VarType{ str } {}
    SExpr(Boolean boolean): VarType{ boolean } {}
    SExpr(Undefined): VarType{ Undefined{} } {}

    // Pre: all pointers must be valid (no nullptrs allowed)
    const SExpr* clone(Core::Allocator<SExpr>& pool) const;

    // Pre: all pointers must be valid (no nullptrs allowed)
    std::string toString() const;

    // Pre: all pointers must be valid (no nullptrs allowed)
    std::pair<bool, std::string> toStringUntil(const SExpr* p) const;

    static std::string escapeString(const std::string& s);
    static std::string unescapeString(const std::string& s);
  };

}

#endif // SEXPR_HPP_
