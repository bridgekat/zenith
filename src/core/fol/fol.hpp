// Core :: FOLContext, FOLForm

#ifndef FOL_HPP_
#define FOL_HPP_

#include <string>
#include <utility>
#include <vector>
#include "../context.hpp"
#include "../expr.hpp"

// clang-format off
namespace Core {

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

    const Tag tag;
    union {
      struct { const Expr* e; } unary;       // Not, Other
      struct { const Expr* l, * r; } binary; // Equals, And, Or, Implies, Iff
      struct { const Expr* r; } binder;      // Forall, Exists, Unique
    };
    // I have to move this outside the union, or it will be impossible to make a copy constructor...
    const std::string s{};

    FOLForm(Tag tag): tag(tag), unary{nullptr} {
      switch (tag) { case True: case False: return; default: unreachable; }
    }
    FOLForm(Tag tag, const Expr* e): tag(tag), unary{e} {
      switch (tag) { case Not: case Other: return; default: unreachable; }
    }
    FOLForm(Tag tag, const Expr* l, const Expr* r): tag(tag), binary{l, r} {
      switch (tag) { case Equals: case And: case Or: case Implies: case Iff: return; default: unreachable; }
    }
    FOLForm(Tag tag, std::string s, const Expr* r): tag(tag), binder{r}, s(std::move(s)) {
      switch (tag) { case Forall: case Exists: case Unique: return; default: unreachable; }
    }
    FOLForm(const FOLForm&) = default;

    // Try matching on an expression.
    // If it has first-order form (e.g. the principal connective is "and") then return it.
    // Otherwise returns `Other`.
    static FOLForm fromExpr(const Expr* e) noexcept;

    // Convert to expresssion (lifetime bounded by subexpression pointers and `pool`).
    const Expr* toExpr(Allocator<Expr>& pool) const;

    // Splits "P iff Q" into "P implies Q" and "Q implies P"
    // Pre (checked): `tag` is `Iff`
    std::pair<const Expr*, const Expr*> splitIff(Allocator<Expr>& pool) const;

    // Splits "unique x, P" into "exists x, P" and "forall x, P implies (forall y, P implies x = y)"
    // Pre (checked): `tag` is `Unique`
    std::pair<const Expr*, const Expr*> splitUnique(Allocator<Expr>& pool) const;

    // Render as much as possible the "root part" of an expression as first-order formula
    std::string toString(const Context& ctx, std::vector<std::string>& stk) const;
    std::string toString(const Context& ctx) const {
      std::vector<std::string> stk;
      return toString(ctx, stk);
    }
  };

}

#endif // FOL_HPP_
