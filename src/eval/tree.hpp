// Eval :: Matcher, Tree, Nil, Cons, VarType...

#ifndef TREE_HPP_
#define TREE_HPP_

#include <any>
#include <compare>
#include <cstdint>
#include <string>
#include <utility>
#include <variant>
#include <core/base.hpp>

namespace Eval {

  // See: https://en.cppreference.com/w/cpp/utility/variant/visit
  template <typename... Ts>
  struct Matcher: Ts... {
    using Ts::operator()...;
  };
  template <typename... Ts>
  Matcher(Ts...) -> Matcher<Ts...>;

  // A generic representation for different tree structures.
  // Intended for use as an exchange / transformation format.
  // `T` must be the variant type itself or some derived class;
  // `Ts...` denote all possible types of an atom.
  // (C++23 will allow direct visitation on classes derived from `std::variant`...)
  template <typename T, typename... Ts>
  struct BasicTree;
  template <typename T>
  struct BasicNil {
    bool operator==(const BasicNil&) const noexcept = default;
  };
  template <typename T>
  struct BasicCons {
    T *head, *tail;
    bool operator==(const BasicCons& r) const noexcept { return *head == *r.head && *tail == *r.tail; };
  };
  template <typename T, typename... Ts>
  struct BasicTree {
    std::variant<BasicNil<T>, BasicCons<T>, Ts...> v{};
    bool operator==(const BasicTree&) const noexcept = default;
  };

  // clang-format off
  // Concrete atom types for Tree
  class Tree;
  struct Symbol  { std::string val;           bool operator==(const Symbol&)   const noexcept = default; };
  struct Prim    { size_t id;                 bool operator==(const Prim&)     const noexcept = default; };
  struct Nat64   { uint64_t val;              bool operator==(const Nat64&)    const noexcept = default; };
  struct String  { std::string val;           bool operator==(const String&)   const noexcept = default; };
  struct Bool    { bool val;                  bool operator==(const Bool&)     const noexcept = default; };
  struct Unit    {                            bool operator==(const Unit&)     const noexcept = default; };
  struct Closure { Tree* env, * formal, * es; bool operator==(const Closure&)  const noexcept = default; };
  struct Native  { std::any val;              bool operator==(const Native& r) const noexcept { return this == &r; } };
  // clang-format on

  class Tree;
  using Nil = BasicNil<Tree>;
  using Cons = BasicCons<Tree>;
  using VarType = BasicTree<Tree, Symbol, Prim, Nat64, String, Bool, Unit, Closure, Native>;

  // Main Tree type
  // Pre (for all methods): there is no "cycle" throughout the tree / DAG
  // Pre & invariant (for all methods): all pointers (in the "active variant") are valid
  class Tree: public VarType {
  public:
    // Convenient constructors
    Tree(Tree* l, Tree* r):
      VarType{
        Cons{l, r}
    } {}
    Tree(Nil const& x): VarType{x} {}
    Tree(Cons const& x): VarType{x} {}
    Tree(Symbol const& x): VarType{x} {}
    Tree(Prim const& x): VarType{x} {}
    Tree(Nat64 const& x): VarType{x} {}
    Tree(String const& x): VarType{x} {}
    Tree(Bool const& x): VarType{x} {}
    Tree(Unit const& x): VarType{x} {}
    Tree(Closure const& x): VarType{x} {}
    Tree(Native const& x): VarType{x} {}
    bool operator==(const Tree&) const noexcept = default;

    Tree* clone(Core::Allocator<Tree>& pool, Tree* nil, Tree* unit) const;

    std::string toString() const;
    std::pair<bool, std::string> toStringUntil(const Tree* p) const;

    static std::string escapeString(const std::string& s);
    static std::string unescapeString(const std::string& s);
  };

  /*
  // A thread-local temporary allocator instance for `Tree`
  // Should be cleared only by outermost level code
  inline Core::Allocator<Tree>& temp() {
    thread_local Core::Allocator<Tree> pool;
    return pool;
  }
  */

}

#endif // TREE_HPP_
