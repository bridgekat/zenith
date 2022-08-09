// Core :: Expr, InvalidExpr

#ifndef EXPR_HPP_
#define EXPR_HPP_

#include <cstdint>
#include <stdexcept>
#include "base.hpp"
#include "context.hpp"

namespace Core {

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

    const Tag tag;
    union {
      struct { const SortTag tag; } sort;
      struct { const VarTag tag; const uint64_t id; } var;
      struct { const Expr *l, *r; } app;
      struct { const std::string s; const Expr *t, *r; } lam;
      struct { const std::string s; const Expr *t, *r; } pi;
    };
    // clang-format on

    // The constructors below guarantee that all pointers in the "active variant" are valid, if parameters are valid
    Expr(SortTag sorttag): tag(Sort), sort{sorttag} {}
    Expr(VarTag vartag, uint64_t id): tag(Var), var{vartag, id} {}
    Expr(const Expr* l, const Expr* r): tag(App), app{l, r} {}
    Expr(LamTag, std::string s, const Expr* t, const Expr* r): tag(Lam), lam{std::move(s), t, r} {}
    Expr(PiTag, std::string s, const Expr* t, const Expr* r): tag(Pi), pi{std::move(s), t, r} {}

    // Immutability + non-trivial members in union = impossible to make a copy constructor...
    Expr(const Expr&) = delete;

    // Destructor needed for the `std::string` in union
    ~Expr() {
      switch (tag) {
        case Sort: return;
        case Var: return;
        case App: return;
        case Lam: lam.s.~basic_string(); return;
        case Pi: pi.s.~basic_string(); return;
      }
      unreachable;
    }

    // Deep copy whole expression to `pool`
    // O(size)
    const Expr* clone(Allocator<Expr>& pool) const;

    // Syntactical equality and hash code (up to alpha-renaming!)
    // O(size)
    bool operator==(const Expr& rhs) const noexcept;
    bool operator!=(const Expr& rhs) const noexcept { return !(*this == rhs); }
    size_t hash() const noexcept;

    // Give unnamed bound variables a random name
    static std::string newName(size_t i);

    // Print
    // `names` will be unchanged
    // O(size)
    std::string toString(const Context& ctx, std::vector<std::string>& stk) const;
    std::string toString(const Context& ctx) const {
      std::vector<std::string> stk;
      return toString(ctx, stk);
    }

    // Controls the Π-formation rule
    constexpr static SortTag imax(SortTag s, SortTag t) {
      if (s == Expr::SProp || t == Expr::SProp) return Expr::SProp;
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
    const Expr* checkType(const Context& ctx, Allocator<Expr>& pool) const {
      std::vector<const Expr*> stk;
      std::vector<std::string> names;
      return checkType(ctx, pool, stk, names);
    }

    // `stk` and `names` will be unchanged
    const Expr* checkType(
      const Context& ctx, Allocator<Expr>& pool, std::vector<const Expr*>& stk, std::vector<std::string>& names
    ) const;

    // Modification (lifetime of the resulting expression is bounded by `this` and `pool`)
    // n = (number of binders on top of current node)
    template <typename F>
    const Expr* updateVars(F f, Allocator<Expr>& pool, uint64_t n = 0) const {
      using enum Tag; // These are needed to avoid ICE on gcc...
      using enum LamTag;
      using enum PiTag;
      switch (tag) {
        case Sort: return this;
        case Var: return f(n, this);
        case App: {
          const auto l = app.l->updateVars(f, pool, n);
          const auto r = app.r->updateVars(f, pool, n);
          return (l == app.l && r == app.r) ? this : make(pool, l, r);
        }
        case Lam: {
          const auto t = lam.t->updateVars(f, pool, n);
          const auto r = lam.r->updateVars(f, pool, n + 1);
          return (t == lam.t && r == lam.r) ? this : make(pool, LLam, lam.s, t, r);
        }
        case Pi: {
          const auto t = pi.t->updateVars(f, pool, n);
          const auto r = pi.r->updateVars(f, pool, n + 1);
          return (t == pi.t && r == pi.r) ? this : make(pool, PPi, pi.s, t, r);
        }
      }
      unreachable;
    }

    // Make a free variable into an overflow variable.
    // Lifetime of the resulting expression is bounded by `this` and `pool`.
    const Expr* makeBound(uint64_t id, Allocator<Expr>& pool) const {
      const Expr* v = nullptr;
      return updateVars(
        [id, &v, &pool](uint64_t n, const Expr* x) {
          return (x->var.tag == VFree && x->var.id == id) ? (v ? v : v = make(pool, VBound, n)) : x;
        },
        pool
      );
    }

    // Replace one overflow variable by an expression.
    // Lifetime of the resulting expression is bounded by `this`, `t` and `pool`.
    const Expr* makeReplace(const Expr* t, Allocator<Expr>& pool) const {
      return updateVars(
        [t](uint64_t n, const Expr* x) { return (x->var.tag == VBound && x->var.id == n) ? t : x; },
        pool
      );
    }

    // Performs applicative-order beta-reduction.
    // If the original expression is well-typed, the resulting expression will have the same type.
    // Note that this function is only a syntactic operation, and does not check well-formedness.
    // It does not terminate on inputs like (\x => x x x) (\x => x x x).
    // If expression is well-typed, worst case time complexity is O(size * 2^size).
    // Lifetime of the resulting expression is bounded by `this` and `pool`.
    const Expr* reduce(Allocator<Expr>& pool) const;

    // Returns the number of symbols of the expression.
    size_t size() const noexcept;

    // Check if given variable is in the subtree.
    bool occurs(VarTag vartag, uint64_t id) const noexcept;

    // Returns the maximum undetermined variable ID + 1.
    size_t numMeta() const noexcept;

    // Check if the expression does not contain undetermined variables.
    bool isGround() const noexcept { return numMeta() == 0; }

    // Convenient constructor
    template <typename... Ts>
    inline static const Expr* make(Allocator<Expr>& pool, Ts&&... args) {
      return pool.emplaceBack(std::forward<Ts>(args)...);
    }
  };

  // A thread-local temporary allocator instance for `Expr`
  // Should be cleared only by outermost level code
  inline Allocator<Expr>& temp() {
    thread_local Allocator<Expr> pool;
    return pool;
  }

  // An exception class representing checking failure
  struct InvalidExpr: public std::runtime_error {
    const Expr* e;
    explicit InvalidExpr(const std::string& s, const Context& ctx, const Expr* e):
      std::runtime_error("Invalid expression, " + s + ": " + e->toString(ctx)), e(e) {}
    InvalidExpr(const InvalidExpr&) = default;
    InvalidExpr& operator=(const InvalidExpr&) = default;
  };

}

#endif // EXPR_HPP_
