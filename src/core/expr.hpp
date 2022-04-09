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
    enum class Tag: uint32_t { Sort, Var, App, Lam, Pi }; using enum Tag;
    enum class SortTag: uint32_t { SProp, SType }; using enum SortTag; 
    enum class VarTag: uint32_t { VBound, VFree, VMeta }; using enum VarTag;
    enum class LamTag: uint32_t { LLam }; using enum LamTag;
    enum class PiTag: uint32_t { PPi }; using enum PiTag;

    // Switching active variant is not supported yet
    const Tag tag;
    union {
      struct { SortTag tag; } sort;
      struct { VarTag tag; uint64_t id; } var;
      struct { Expr* l; Expr* r; } app;
      struct { std::string s; Expr* t; Expr* r; } lam;
      struct { std::string s; Expr* t; Expr* r; } pi;
    };

    // The constructors below guarantee that all nonzero pointers in the "active variant" are valid
    Expr(SortTag sorttag): tag(Sort), sort{ sorttag } {}
    Expr(VarTag vartag, uint64_t id): tag(Var), var{ vartag, id } {}
    Expr(Expr* l, Expr* r): tag(App), app{ l, r } {}
    Expr(LamTag, const std::string& s, Expr* t, Expr* r): tag(Lam), lam{ s, t, r } {}
    Expr(PiTag, const std::string& s, Expr* t, Expr* r): tag(Pi), pi{ s, t, r } {}

    // Copy constructor is shallow copy
    Expr(const Expr& r): tag(r.tag) {
      switch (tag) {
        case Sort: sort = r.sort; break;
        case Var: var = r.var; break;
        case App: app = r.app; break;
        case Lam: new (&lam.s) std::string(r.lam.s); lam.t = r.lam.t; lam.r = r.lam.r; break;
        case Pi: new (&pi.s) std::string(r.pi.s); pi.t = r.pi.t; pi.r = r.pi.r; break;
      }
    }

    // Destructor needed for std::string in union
    ~Expr() {
      switch (tag) {
        case Sort: case Var: case App: break;
        case Lam: lam.s.~basic_string(); break;
        case Pi: pi.s.~basic_string(); break;
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
    // `names` will be unchanged
    // O(size)
    std::string toString(const Context& ctx, std::vector<std::string>& stk) const;
    std::string toString(const Context& ctx) const {
      std::vector<std::string> stk;
      return toString(ctx, stk);
    }

    // Check if the subtree is a well-formed term (1), type (2) or proof (3).
    // (1) Returns a well-formed, beta-reduced expression of type `Type`, representing the type of the term;
    // (2) Returns `Type` itself;
    // (3) Returns a well-formed, beta-reduced expression of type `Prop`, representing the proposition it proves.
    // Throws exception on failure
    // Pre: all nonzero pointers are valid
    // `stk` and `names` will be unchanged
    Expr* checkType(const Context& ctx, Allocator<Expr>& pool, std::vector<const Expr*>& stk, std::vector<std::string>& names) const;
    Expr* checkType(const Context& ctx, Allocator<Expr>& pool) const {
      std::vector<const Expr*> stk;
      std::vector<std::string> names;
      return checkType(ctx, pool, stk, names);
    }

    // Modification (deep copying whole expression to `pool`)
    // Pre: all nonzero pointers are valid
    // n = (number of binders on top of current node)
    template <typename F>
    Expr* updateVars(uint64_t n, Allocator<Expr>& pool, const F& f) const {
      using enum Tag;
      switch (tag) {
        case Sort: return make(pool, sort.tag);
        case Var: return f(n, this);
        case App: return make(pool, app.l? app.l->updateVars(n, pool, f) : nullptr, app.r? app.r->updateVars(n, pool, f) : nullptr);
        case Lam: return make(pool, lam.s, lam.t? lam.t->updateVars(n, pool, f) : nullptr, lam.r? lam.r->updateVars(n + 1, pool, f) : nullptr);
        case Pi: return make(pool, pi.s, pi.t? pi.t->updateVars(n, pool, f) : nullptr, pi.r? pi.r->updateVars(n + 1, pool, f) : nullptr);
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
    // O(size)
    size_t size() const noexcept;

    // Check if given variable is in the subtree
    // Pre: all nonzero pointers are valid
    // O(size)
    bool occurs(VarTag vartag, uint64_t id) const noexcept;

    // Returns the maximum undetermined variable ID + 1
    // O(size)
    size_t numUndetermined() const noexcept;

    // Check if the expression does not contain undetermined variables
    // O(size)
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
    InvalidExpr(const std::string& s, const Context& ctx, const Expr* e): CheckFailure("Invalid expression, " + s + ": " + e->toString(ctx), e) {}
  };
  struct InvalidProof: public CheckFailure {
    InvalidProof(const std::string& s, const Context& ctx, const Expr* e): CheckFailure("Invalid proof, " + s + ": " + e->toString(ctx), e) {}
  };

}

#endif // EXPR_HPP_
