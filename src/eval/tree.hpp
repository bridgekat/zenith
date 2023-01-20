// Eval :: Matcher, Tree, Nil, Cons, VarType...

#ifndef TREE_HPP_
#define TREE_HPP_

#include <any>
#include <compare>
#include <cstdint>
#include <string>
#include <utility>
#include <variant>
#include <common.hpp>

namespace Eval {

  // clang-format off
  // Concrete atom types for Tree
  class Tree;
  struct Symbol  { std::string val;           auto operator==(Symbol const&)   const -> bool = default; };
  struct Prim    { size_t id;                 auto operator==(Prim const&)     const -> bool = default; };
  struct Nat64   { uint64_t val;              auto operator==(Nat64 const&)    const -> bool = default; };
  struct String  { std::string val;           auto operator==(String const&)   const -> bool = default; };
  struct Bool    { bool val;                  auto operator==(Bool const&)     const -> bool = default; };
  struct Unit    {                            auto operator==(Unit const&)     const -> bool = default; };
  struct Closure { Tree* env, * formal, * es; auto operator==(Closure const&)  const -> bool = default; };
  struct Native  { std::any val;              auto operator==(Native const& r) const -> bool { return &val == &r.val; } };
  // clang-format on

  struct Nil {
    auto operator==(Nil const&) const -> bool = default;
  };

  struct Cons {
    Tree *head, *tail;
    auto operator==(Cons const& r) const -> bool;
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

    auto clone(Allocator<Tree>& pool, Tree* nil, Tree* unit) const -> Tree*;

    auto toString() const -> std::string;
    auto toStringUntil(Tree const* p) const -> std::pair<bool, std::string>;

    static auto escapeString(std::string const& s) -> std::string;
    static auto unescapeString(std::string const& s) -> std::string;
  };

  inline auto Cons::operator==(Cons const& r) const -> bool { return *head == *r.head && *tail == *r.tail; };

  /*
  // A thread-local temporary allocator instance for `Tree`
  // Should be cleared only by outermost level code
  inline Allocator<Tree>& temp() {
    thread_local Allocator<Tree> pool;
    return pool;
  }
  */

}

#endif // TREE_HPP_
