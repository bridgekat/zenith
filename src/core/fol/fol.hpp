// Core :: FOLContext, FOLForm

#ifndef FOL_HPP_
#define FOL_HPP_

#include <string>
#include "../context.hpp"
#include "../expr.hpp"


namespace Core {

  // Specialized context for first-order logic, with pre-defined constants
  class FOLContext: public Context {
  public:
    // Code consistency (checked at runtime): if you change this, you may have to update `FOLContext::FOLContext()`
    // Code consistency (unchecked): also update relevant parts of `FOLForm` and its uses
    enum Constant: uint64_t { SetVar, Arbitrary, Equals, True, False, Not, And, Or, Implies, Iff, Forall, Exists, Unique };

    FOLContext();
  };

  class FOLForm {
  public:
    // "Other" means either atomic or not first-order
    enum class Tag: uint32_t { True, False, Not, And, Or, Implies, Iff, Forall, Exists, Unique, Other };
    using enum Tag;

    // Immutable
    const Tag tag;
    union {
      struct { const Expr* l; } unary;       // Not
      struct { const Expr* l, * r; } binary; // And, Or, Implies, Iff
      struct { const Expr* r; } binder;      // Forall, Exists, Unique
    };
    // I have to move this outside the union, or it will be impossible to make a copy constructor...
    const std::string s{};

    explicit
    FOLForm(Tag tag): tag(tag) {
      switch (tag) {
        case True: case False: case Other: break;
        default: throw Unreachable();
      }
    }
    FOLForm(Tag tag, const Expr* l): tag(tag), unary{ l } {
      switch (tag) {
        case Not: break;
        default: throw Unreachable();
      }
    }
    FOLForm(Tag tag, const Expr* l, const Expr* r): tag(tag), binary{ l, r } {
      switch (tag) {
        case And: case Or: case Implies: case Iff: break;
        default: throw Unreachable();
      }
    }
    FOLForm(Tag tag, const std::string& s, const Expr* r): tag(tag), binder{ r }, s(s) {
      switch (tag) {
        case Forall: case Exists: case Unique: break;
        default: throw Unreachable();
      }
    }
    FOLForm(const FOLForm&) = default;

    // Pre: `e` is well-typed expression
    static FOLForm fromExpr(const Expr* e) noexcept;
    // Pre (checked): `tag` is not `Other`
    const Expr* toExpr(Allocator<Expr>& pool) const;
  };

}

#endif // FOL_HPP_
