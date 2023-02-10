// Core :: FOLContext, FOLForm

#ifndef APIMU_CORE_FOL_HPP
#define APIMU_CORE_FOL_HPP

#include <string>
#include <utility>
#include <vector>
#include "../context.hpp"
#include "../expr.hpp"

// clang-format off
namespace apimu::core {
#include "macros_open.hpp"

  // Specialized context for first-order logic, with pre-defined constants
  class FOLContext: public Context {
  public:
    // Code consistency (checked at runtime): if you change this, you may have to update `FOLContext::FOLContext()`
    // Code consistency (unchecked): also update relevant parts of `FOLForm` and its uses
    enum Constant: uint64_t { SetVar, Arbitrary, Equals, True, False, Not, And, Or, Implies, Iff, Forall, Exists, Unique };

    FOLContext();
  };

  // Immutable.
  class FOLForm {
  public:
    enum class Tag: uint32_t { Other, Equals, True, False, Not, And, Or, Implies, Iff, Forall, Exists, Unique };
    using enum Tag;

    Tag const tag;
    union {
      struct { Expr const* e; } unary;       // Not, Other
      struct { Expr const* l, * r; } binary; // Equals, And, Or, Implies, Iff
      struct { Expr const* r; } binder;      // Forall, Exists, Unique
    };
    // I have to move this outside the union, or it will be impossible to make a copy constructor...
    std::string const s;

    FOLForm(Tag tag): tag(tag), unary{nullptr} {
      switch (tag) { case True: case False: return; default: unreachable; }
    }
    FOLForm(Tag tag, Expr const* e): tag(tag), unary{e} {
      switch (tag) { case Not: case Other: return; default: unreachable; }
    }
    FOLForm(Tag tag, Expr const* l, Expr const* r): tag(tag), binary{l, r} {
      switch (tag) { case Equals: case And: case Or: case Implies: case Iff: return; default: unreachable; }
    }
    FOLForm(Tag tag, std::string s, Expr const* r): tag(tag), binder{r}, s(std::move(s)) {
      switch (tag) { case Forall: case Exists: case Unique: return; default: unreachable; }
    }

    // Try matching on an expression.
    // If it has first-order form (e.g. the principal connective is "and") then return it.
    // Otherwise returns `Other`.
    static auto fromExpr(Expr const* e) noexcept -> FOLForm;

    // Convert to expresssion (lifetime bounded by subexpression pointers and `pool`).
    auto toExpr(Allocator<Expr>& pool) const -> Expr const*;

    // Splits "P iff Q" into "P implies Q" and "Q implies P"
    // Pre (checked): `tag` is `Iff`
    auto splitIff(Allocator<Expr>& pool) const -> std::pair<Expr const*, Expr const*>;

    // Splits "unique x, P" into "exists x, P" and "forall x, P implies (forall y, P implies x = y)"
    // Pre (checked): `tag` is `Unique`
    auto splitUnique(Allocator<Expr>& pool) const -> std::pair<Expr const*, Expr const*>;

    // Render as much as possible the "root part" of an expression as first-order formula
    auto toString(Context const& ctx, std::vector<std::string>& stk) const -> std::string;
    auto toString(Context const& ctx) const -> std::string {
      std::vector<std::string> stk;
      return toString(ctx, stk);
    }
  };

#include "macros_close.hpp"
}

#endif // APIMU_CORE_FOL_HPP
