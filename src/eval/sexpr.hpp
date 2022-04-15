// Eval :: Matcher, SExpr, Nil, Cons, VarType...

#ifndef SEXPR_HPP_
#define SEXPR_HPP_

#include <cstdint>
#include <string>
#include <variant>
#include <utility>
#include <compare>
#include <any>
#include <core/base.hpp>


namespace Eval {

  // See: https://en.cppreference.com/w/cpp/utility/variant/visit
  template <typename... Ts> struct Matcher: Ts... { using Ts::operator()...; };
  template <typename... Ts> Matcher(Ts...) -> Matcher<Ts...>;

  // A generic representation for different tree structures.
  // Intended for use as an exchange / transformation format.
  // `T` must be the variant type itself or some derived class;
  // `Ts...` denote all possible types of an atom.
  // (C++23 will allow direct visitation on classes derived from `std::variant`...)
  template <typename T, typename... Ts>
  struct BasicSExpr;
  template <typename T>
  struct BasicNil {
    bool operator==(const BasicNil&) const noexcept = default;
  };
  template <typename T>
  struct BasicCons {
    T* head, * tail;
    bool operator==(const BasicCons& r) const noexcept { return *head == *r.head && *tail == *r.tail; };
  };
  template <typename T, typename... Ts>
  struct BasicSExpr {
    std::variant<BasicNil<T>, BasicCons<T>, Ts...> v{};
    bool operator==(const BasicSExpr&) const noexcept = default;
  };

  // Concrete atom types for SExpr
  class SExpr;
  struct Symbol {
    std::string s;
    bool operator==(const Symbol& r) const noexcept = default;
  };
  using Number = int64_t;
  using String = std::string;
  enum class Boolean: uint8_t { False, True }; // Avoid casting other types to boolean
  enum class Undefined: uint8_t { Undefined };
  struct Closure {
    SExpr* env, * formal, * es;
    bool operator==(const Closure&) const noexcept = default;
  };
  struct Builtin {
    size_t index;
    bool operator==(const Builtin&) const noexcept = default;
  };
  struct Native {
    std::any val;
    bool operator==(const Native& r) const noexcept { return &val == &r.val; }
  };

  // Main SExpr type
  class SExpr;
  using Nil = BasicNil<SExpr>;
  using Cons = BasicCons<SExpr>;
  using VarType = BasicSExpr<SExpr, Symbol, Number, String, Boolean, Undefined, Closure, Builtin, Native>;

  // Pre (for all methods): there is no "cycle" throughout the tree / DAG
  // Pre & invariant (for all methods): all pointers (in the "active variant") are valid
  class SExpr: public VarType {
  public:
    // Convenient constructors
    SExpr(): VarType{} {}
    SExpr(SExpr* l, SExpr* r): VarType{ Cons{ l, r } } {}
    SExpr(Nil): VarType{ Nil{} } {}
    SExpr(Cons const& cons):  VarType{ cons } {}
    SExpr(Symbol const& sym): VarType{ sym } {}
    SExpr(Number const& num): VarType{ num } {}
    SExpr(String const& str): VarType{ str } {}
    SExpr(Boolean boolean): VarType{ boolean } {}
    SExpr(Undefined): VarType{ Undefined{} } {}
    SExpr(Closure const& cl): VarType{ cl } {}
    SExpr(Builtin const& bi): VarType{ bi } {}
    SExpr(Native const& nat): VarType{ nat } {}
    bool operator==(const SExpr& r) const noexcept = default;

    SExpr* clone(Core::Allocator<SExpr>& pool, SExpr* nil, SExpr* undefined) const;

    std::string toString() const;
    std::pair<bool, std::string> toStringUntil(const SExpr* p) const;

    static std::string escapeString(const std::string& s);
    static std::string unescapeString(const std::string& s);
  };

  /*
  // A thread-local temporary allocator instance for `SExpr`
  // Should be cleared only by outermost level code
  inline Core::Allocator<SExpr>& temp() {
    thread_local Core::Allocator<SExpr> pool;
    return pool;
  }
  */

}

#endif // SEXPR_HPP_
