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
  template <typename T, typename... Ts>
  struct BasicSExpr;
  template <typename T, typename... Ts>
  struct BasicNil {
    bool operator==(const BasicNil&) const { return true; };
    bool operator!=(const BasicNil&) const { return false; };
  };
  template <typename T, typename... Ts>
  struct BasicCons {
    T* head, * tail;
    BasicCons(T* head, T* tail): head(head), tail(tail) {}
    bool operator==(const BasicCons& r) const { return *head == *r.head && *tail == *r.tail; };
    bool operator!=(const BasicCons& r) const { return *head != *r.head || *tail != *r.tail; };
  };
  template <typename T, typename... Ts>
  struct BasicSExpr {
    std::variant<BasicNil<T, Ts...>, BasicCons<T, Ts...>, Ts...> v{};
    bool operator==(const BasicSExpr& r) const { return v == r.v; };
    bool operator!=(const BasicSExpr& r) const { return v != r.v; };
  };

  // Concrete atom types for SExpr
  class SExpr;
  struct Symbol {
    std::string s;
    Symbol(const std::string& s): s(s) {}
    bool operator==(const Symbol& r) const { return s == r.s; };
    bool operator!=(const Symbol& r) const { return s != r.s; };
  };
  using Number = int64_t;
  using String = std::string;
  using Boolean = bool;
  using Undefined = std::monostate;
  struct Closure {
    SExpr* env, * formal, * es;
    Closure(SExpr* env, SExpr* formal, SExpr* es): env(env), formal(formal), es(es) {}
    bool operator==(const Closure& r) const { return env == r.env && formal == r.formal && es == r.es; };
    bool operator!=(const Closure& r) const { return env != r.env || formal != r.formal || es != r.es; };
  };

  // Main SExpr type
  class SExpr;
  using Nil = BasicNil<SExpr, Symbol, Number, String, Boolean, Undefined, Closure>;
  using Cons = BasicCons<SExpr, Symbol, Number, String, Boolean, Undefined, Closure>;
  using VarType = BasicSExpr<SExpr, Symbol, Number, String, Boolean, Undefined, Closure>;

  // Pre (for all methods): there is no "cycle" throughout the tree / DAG
  // Pre & invariant (for all methods): all pointers (in the "active variant") are valid
  class SExpr: public VarType {
  public:
    // Convenient constructors
    SExpr(): VarType{} {}
    SExpr(SExpr* l, SExpr* r): VarType{ Cons(l, r) } {}
    SExpr(Nil): VarType{} {}
    SExpr(Cons const& cons): VarType{ cons } {}
    SExpr(Symbol const& sym): VarType{ sym } {}
    SExpr(Number const& num): VarType{ num } {}
    SExpr(String const& str): VarType{ str } {}
    SExpr(Boolean boolean): VarType{ boolean } {}
    SExpr(Undefined): VarType{ Undefined() } {}
    SExpr(Closure const& cl): VarType { cl } {}

    SExpr* clone(Core::Allocator<SExpr>& pool) const;

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
