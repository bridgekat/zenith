#ifndef APIMU_CORE_EXPR_HPP
#define APIMU_CORE_EXPR_HPP

#include <cstdint>
#include <stdexcept>
#include <common.hpp>
#include "context.hpp"

namespace apimu::core {
#include "macros_open.hpp"

  // Expression node, and related syntactic operations.
  // Immutable.
  // Pre (for all methods): there is no "cycle" throughout the tree / DAG
  // Pre & invariant (for all methods): all pointers (in the "active variant") are valid
  // Will just stick to this old-fashioned tagged union approach until C++ admits a better way to represent sum types
  //   (`std::variant` + `std::visit` are said to have severe performance issue...)
  class Expr {
  public:
    // clang-format off
    enum class Tag: uint32_t { Sort, Var, App, Lam, Pi }; using enum Tag;
    enum class SortTag: uint32_t { SProp, SType, SKind }; using enum SortTag;
    enum class VarTag: uint32_t { VBound, VFree, VMeta }; using enum VarTag;
    enum class LamTag: uint32_t { LLam }; using enum LamTag;
    enum class PiTag: uint32_t { PPi }; using enum PiTag;

    Tag const tag;
    union {
      struct { SortTag const tag; } sort;
      struct { VarTag const tag; uint64_t const id; } var;
      struct { Expr const *l, *r; } app;
      struct { std::string const s; Expr const *t, *r; } lam;
      struct { std::string const s; Expr const *t, *r; } pi;
    };
    // clang-format on

    // The constructors below guarantee that all pointers in the "active variant" are valid, if parameters are valid
    Expr(SortTag sorttag):
        tag(Sort),
        sort{sorttag} {}

    Expr(VarTag vartag, uint64_t id):
        tag(Var),
        var{vartag, id} {}

    Expr(Expr const* l, Expr const* r):
        tag(App),
        app{l, r} {}

    Expr(LamTag, std::string s, Expr const* t, Expr const* r):
        tag(Lam),
        lam{std::move(s), t, r} {}

    Expr(PiTag, std::string s, Expr const* t, Expr const* r):
        tag(Pi),
        pi{std::move(s), t, r} {}

    // Immutability + non-trivial members in union = impossible to make a copy constructor...
    Expr(Expr const&) = delete;
    Expr(Expr&&) = delete;
    auto operator=(Expr const&) -> Expr& = delete;
    auto operator=(Expr&&) -> Expr& = delete;

    // Destructor needed for the `std::string` in union
    ~Expr() {
      switch (tag) {
        case Sort:
          return;
        case Var:
          return;
        case App:
          return;
        case Lam:
          lam.s.~basic_string();
          return;
        case Pi:
          pi.s.~basic_string();
          return;
      }
      unreachable;
    }

    // Deep copy whole expression to `pool`
    // O(size)
    auto clone(Allocator<Expr>& pool) const -> Expr const*;

    // Syntactical equality and hash code (up to alpha-renaming!)
    // O(size)
    auto operator==(Expr const& rhs) const noexcept -> bool;
    auto operator!=(Expr const& rhs) const noexcept -> bool {
      return !(*this == rhs);
    }
    auto hash() const noexcept -> size_t;

    // Give unnamed bound variables a random name
    static auto newName(size_t i) -> std::string;

    // Print
    // `names` will be unchanged
    // O(size)
    auto toString(Context const& ctx, std::vector<std::string>& stk) const -> std::string;
    auto toString(Context const& ctx) const -> std::string {
      std::vector<std::string> stk;
      return toString(ctx, stk);
    }

    // Controls the Π-formation rule
    static constexpr auto imax(SortTag s, SortTag t) -> SortTag {
      if (s == Expr::SProp || t == Expr::SProp)
        return Expr::SProp;
      // Mid: `s` and `t` are `Expr::SType` or `Expr::SKind`
      return (s == Expr::SKind || t == Expr::SKind) ? Expr::SKind : Expr::SType;
    }

    // Check if the subtree is a well-formed term (1), type (2), proof (3) or formula (4).
    // (1) Returns a well-formed, beta-reduced expression of type `Type`, representing the type of the term;
    // (2) Returns `Type` itself;
    // (3) Returns a well-formed, beta-reduced expression of type `Prop`, representing the proposition it proves;
    // (4) Returns `Prop` itself.
    // (Returned pointer lifetime is bound by `this`, `ctx` and `pool`!)
    // Throws exception on failure
    auto checkType(Context const& ctx, Allocator<Expr>& pool) const -> Expr const* {
      std::vector<Expr const*> stk;
      std::vector<std::string> names;
      return checkType(ctx, pool, stk, names);
    }

    // `stk` and `names` will be unchanged
    auto checkType(
      Context const& ctx,
      Allocator<Expr>& pool,
      std::vector<Expr const*>& stk,
      std::vector<std::string>& names
    ) const -> Expr const*;

    // Modification (lifetime of the resulting expression is bounded by `this` and `pool`)
    // n = (number of binders on top of current node)
    template <typename F>
    auto updateVars(F f, Allocator<Expr>& pool, uint64_t n = 0) const -> Expr const* {
      using enum Tag; // These are needed to avoid ICE on gcc...
      using enum LamTag;
      using enum PiTag;
      switch (tag) {
        case Sort:
          return this;
        case Var:
          return f(n, this);
        case App: {
          auto const l = app.l->updateVars(f, pool, n);
          auto const r = app.r->updateVars(f, pool, n);
          return (l == app.l && r == app.r) ? this : pool.make(l, r);
        }
        case Lam: {
          auto const t = lam.t->updateVars(f, pool, n);
          auto const r = lam.r->updateVars(f, pool, n + 1);
          return (t == lam.t && r == lam.r) ? this : pool.make(LLam, lam.s, t, r);
        }
        case Pi: {
          auto const t = pi.t->updateVars(f, pool, n);
          auto const r = pi.r->updateVars(f, pool, n + 1);
          return (t == pi.t && r == pi.r) ? this : pool.make(PPi, pi.s, t, r);
        }
      }
      unreachable;
    }

    // Lift overflow variables by `m` levels.
    // Lifetime of the resulting expression is bounded by `this` and `pool`.
    auto lift(uint64_t m, Allocator<Expr>& pool) const -> Expr const* {
      return updateVars(
        [m, &pool](uint64_t n, Expr const* x) -> Expr const* {
          if (x->var.tag == VBound && x->var.id >= n)
            return pool.make(VBound, x->var.id + m);
          return x;
        },
        pool
      );
    }

    // Replace one overflow variable by an expression (i.e. deleting the outermost binder).
    // Lifetime of the resulting expression is bounded by `this`, `t` and `pool`.
    auto makeReplace(Expr const* t, Allocator<Expr>& pool) const -> Expr const* {
      return updateVars(
        [t, &pool](uint64_t n, Expr const* x) -> Expr const* {
          if (x->var.tag == VBound && x->var.id == n)
            return t->lift(n, pool);
          if (x->var.tag == VBound && x->var.id > n)
            return pool.make(VBound, x->var.id - 1);
          return x;
        },
        pool
      );
    }

    // Performs applicative-order beta-reduction.
    // If the original expression is well-typed, the resulting expression will have the same type.
    // Note that this function is only a syntactic operation, and does not check well-formedness.
    // It does not terminate on inputs like (\x => x x x) (\x => x x x).
    // If expression is well-typed, worst case time complexity is O(size * 2^size).
    // Lifetime of the resulting expression is bounded by `this` and `pool`.
    auto reduce(Allocator<Expr>& pool) const -> Expr const*;

    // Returns the number of symbols of the expression.
    auto size() const noexcept -> size_t;

    // Check if given variable is in the subtree.
    auto occurs(VarTag vartag, uint64_t id) const noexcept -> bool;

    // Returns the maximum undetermined variable ID + 1.
    auto numMeta() const noexcept -> size_t;

    // Check if the expression does not contain undetermined variables.
    auto isGround() const noexcept -> bool {
      return numMeta() == 0;
    }
  };

  // A thread-local temporary allocator instance for `Expr`
  // Should be cleared only by outermost level code
  inline auto temp() -> Allocator<Expr>& {
    thread_local Allocator<Expr> pool;
    return pool;
  }

  // An exception class representing checking failure
  class InvalidExpr: public std::runtime_error {
  public:
    Expr const* e;
    InvalidExpr(std::string const& s, Context const& ctx, Expr const* e):
        std::runtime_error("Invalid expression, " + s + ": " + e->toString(ctx)),
        e(e) {}
  };

#include "macros_close.hpp"
}

#endif // APIMU_CORE_EXPR_HPP
