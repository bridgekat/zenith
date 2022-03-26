// Core :: Matcher, SList, SExpr, SNil

#ifndef SEXPR_HPP_
#define SEXPR_HPP_

#include <string>
#include <variant>

namespace Core {

  // See: https://en.cppreference.com/w/cpp/utility/variant/visit
  template <typename... Ts> struct Matcher: Ts... { using Ts::operator()...; };

  // A generic representation for different tree structures.
  // Intended for use as an exchange / transformation format.
  // `Ts...` denotes all possible types of an atom.
  template <typename... Ts> struct SExpr;
  template <typename... Ts> struct SList { SExpr<Ts...>* head{}, * tail{}; };
  template <typename... Ts> struct SExpr { std::variant<Ts..., SList<Ts...>> v = SList<Ts...>{}; };
  template <typename... Ts> constexpr inline SExpr<Ts...> SNil = {};

  // SExpr with string atoms
  using SSExpr = SExpr<std::string>;

}

#endif // SEXPR_HPP_
