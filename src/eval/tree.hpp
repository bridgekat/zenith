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

  // clang-format off
  // Concrete atom types for Tree
  class Tree;
  struct Symbol  { std::string val;           bool operator==(Symbol const&)   const noexcept = default; };
  struct Prim    { size_t id;                 bool operator==(Prim const&)     const noexcept = default; };
  struct Nat64   { uint64_t val;              bool operator==(Nat64 const&)    const noexcept = default; };
  struct String  { std::string val;           bool operator==(String const&)   const noexcept = default; };
  struct Bool    { bool val;                  bool operator==(Bool const&)     const noexcept = default; };
  struct Unit    {                            bool operator==(Unit const&)     const noexcept = default; };
  struct Closure { Tree* env, * formal, * es; bool operator==(Closure const&)  const noexcept = default; };
  struct Native  { std::any val;              bool operator==(Native const& r) const noexcept { return &val == &r.val; } };
  // clang-format on

  struct Nil {
    bool operator==(Nil const&) const noexcept = default;
  };

  struct Cons {
    Tree *head, *tail;
    bool operator==(Cons const& r) const noexcept;
  };

  // Main Tree type
  // Pre (for all methods): there is no "cycle" throughout the tree / DAG
  // Pre & invariant (for all methods): all pointers (in the "active variant") are valid
  class Tree: public std::variant<Nil, Cons, Symbol, Prim, Nat64, String, Bool, Unit, Closure, Native> {
  public:
    using Super = std::variant<Nil, Cons, Symbol, Prim, Nat64, String, Bool, Unit, Closure, Native>;
    using Super::variant;

    Tree():
      Super(Nil{}) {}
    Tree(Tree* l, Tree* r):
      Super(Cons{l, r}) {}

    Tree* clone(Core::Allocator<Tree>& pool, Tree* nil, Tree* unit) const;

    std::string toString() const;
    std::pair<bool, std::string> toStringUntil(Tree const* p) const;

    static std::string escapeString(std::string const& s);
    static std::string unescapeString(std::string const& s);
  };

  inline bool Cons::operator==(Cons const& r) const noexcept { return *head == *r.head && *tail == *r.tail; };

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
