// Core :: Expr, InvalidExpr

#ifndef EXPR_HPP_
#define EXPR_HPP_

#include "base.hpp"
#include "context.hpp"


namespace Core {

  // Expression node, and related syntactic operations
  // Pre (for all methods): there is no "cycle" throughout the tree / DAG
  // Pre & invariant (for all methods): all nonzero pointers (in the "active variant") are valid
  // Will just stick to this old-fashioned tagged union approach until C++ admits a better way to represent sum types
  //   (`std::variant` + `std::visit` are said to have severe performance issues?)
  class Expr {
  public:
    enum class Tag: uint32_t { Type, Var, App, Lam }; using enum Tag;
    enum class TypeTag: uint32_t { TKind, TFun, TVar, TProp }; using enum TypeTag;
    enum class VarTag: uint32_t { VBound, VFree, VMeta }; using enum VarTag;

    // Switching active variant is not supported yet
    const Tag tag;
    union {
      struct { TypeTag tag; Expr* l; Expr* r; } type;
      struct { VarTag tag; uint64_t id; } var;
      struct { Expr* l; Expr* r; } app;
      struct { std::string s; Expr* t; Expr* r; } lam;
    };

    // The constructors below guarantee that all nonzero pointers in the "active variant" are valid
    Expr(TypeTag typetag, Expr* l = nullptr, Expr* r = nullptr): tag(Type), type{ typetag, l, r } {}
    Expr(VarTag vartag, uint64_t id): tag(Var), var{ vartag, id } {}
    Expr(Expr* l, Expr* r): tag(App), app{ l, r } {}
    Expr(const std::string& s, Expr* t, Expr* r): tag(Lam), lam{ s, t, r } {}

    // Copy constructor is shallow copy
    Expr(const Expr& r): tag(r.tag) {
      switch (tag) {
        case Type: type = r.type; break;
        case Var: var = r.var; break;
        case App: app = r.app; break;
        case Lam: new (&lam.s) std::string(r.lam.s); lam.t = r.lam.t; lam.r = r.lam.r; break;
      }
    }

    // Destructor needed for std::string in union
    ~Expr() {
      switch (tag) {
        case Type: case Var: case App: break;
        case Lam: lam.s.~basic_string(); break;
      }
    }

    // Deep copy
    // Pre: all nonzero pointers are valid
    // O(size)
    Expr* clone(Allocator<Expr>& pool) const;

    // Syntactical equality and hash code (up to alpha-renaming!)
    // Pre: all nonzero pointers are valid
    // O(size)
    bool operator==(const Expr& rhs) const noexcept;
    bool operator!=(const Expr& rhs) const noexcept { return !(*this == rhs); }
    size_t hash() const noexcept;

    // Print
    // Pre: all nonzero pointers are valid
    // `stk` will be unchanged
    // O(size)
    std::string toString(const Context& ctx, std::vector<std::string>& stk) const;
    std::string toString(const Context& ctx) const {
      std::vector<std::string> stk;
      return toString(ctx, stk);
    }

    // Check if the subtree is well-formed, and return its type (returned type expression is allocated in `pool`)
    // Throws exception on failure
    // Pre: all nonzero pointers are valid
    // `stk` will be unchanged
    // O(size)
    const Expr* checkType(const Context& ctx, Allocator<Expr>& pool, std::vector<const Expr*>& stk) const;
    const Expr* checkType(const Context& ctx, Allocator<Expr>& pool) const {
      std::vector<const Expr*> stk;
      return checkType(ctx, pool, stk);
    }

    // Modification (deep copying whole expression to `pool`)
    // Pre: all nonzero pointers are valid
    // n = (number of binders on top of current node)
    template <typename F>
    Expr* updateVars(uint64_t n, Allocator<Expr>& pool, const F& f) const {
      using enum Tag;
      switch (tag) {
        case Type: return make(pool, type.tag, type.l? type.l->updateVars(n, pool, f) : nullptr, type.r? type.r->updateVars(n, pool, f) : nullptr);
        case Var: return f(n, this);
        case App: return make(pool, app.l? app.l->updateVars(n, pool, f) : nullptr, app.r? app.r->updateVars(n, pool, f) : nullptr);
        case Lam: return make(pool, lam.s, lam.t? lam.t->updateVars(n, pool, f) : nullptr, lam.r? lam.r->updateVars(n + 1, pool, f) : nullptr);
      }
      throw NotImplemented();
    }

    // Make a free variable into an overflow variable (deep copying whole expression to `pool`)
    Expr* makeBound(uint64_t id, Allocator<Expr>& pool) const {
      return updateVars(0, pool, [id, &pool] (uint64_t n, const Expr* x) {
        return (x->var.tag == VFree && x->var.id == id)? make(pool, VBound, n) : x->clone(pool);
      });
    }

    // Replace one overflow variable by an expression (deep copying whole expression to `pool`)
    Expr* makeReplace(const Expr* t, Allocator<Expr>& pool) const {
      return updateVars(0, pool, [t, &pool] (uint64_t n, const Expr* x) {
        return (x->var.tag == VBound && x->var.id == n)? t->clone(pool) : x->clone(pool);
      });
    }

    // Performs applicative-order beta-reduction (deep copying whole expression to `pool`)
    // Pre: all nonzero pointers are valid
    // If moreover the original expression is well-typed, the resulting expression will have the same type.
    // Note that this function is only a syntactic operation, and does not check well-formedness.
    // It does not terminate on inputs like (\x => x x x) (\x => x x x).
    // If expression is well-typed, worst case time complexity is O(size * 2^size).
    Expr* reduce(Allocator<Expr>& pool) const;

    // Returns the number of symbols of the expression
    size_t size() const noexcept;

    // Check if given variable is in the subtree
    // Pre: all nonzero pointers are valid
    bool occurs(VarTag vartag, uint64_t id) const noexcept;

    // Returns the maximum undetermined variable ID + 1
    size_t numUndetermined() const noexcept;

    // Check if the expression does not contain undetermined variables
    bool isGround() const noexcept { return numUndetermined() == 0; }

    // Convenient constructor
    template <typename... Ts>
    inline static Expr* make(Allocator<Expr>& pool, Ts&&... args) {
      return pool.emplaceBack(std::forward<Ts...>(args...));
    }
  };

  // An exception class representing checking failure
  // TODO: refactor this
  struct InvalidExpr: public CheckFailure {
    InvalidExpr(const string& s, const Context& ctx, const Expr* e): CheckFailure("Invalid expression, " + s + ": " + e->toString(ctx), e) {}
  };

}

#endif // EXPR_HPP_
