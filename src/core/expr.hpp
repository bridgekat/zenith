// Core :: Expr, InvalidExpr

#ifndef EXPR_HPP_
#define EXPR_HPP_

#include "base.hpp"
#include "context.hpp"


namespace Core {

  // Formula (schema) tree node, and related syntactic operations
  // Pre (for all methods): there is no "cycle" throughout the tree
  // Pre & invariant (for all methods): all nonzero pointers (in the "active variant") are valid
  // Will just stick to this old-fashioned tagged union approach before C++ admits a better way to represent sum types
  class Expr {
  public:
    // Alphabet for a first-order language
    enum class Tag: unsigned char {
      EMPTY = 0, // For default values only. EMPTY nodes are not well-formed terms or formulas.
      VAR, TRUE, FALSE, NOT, AND, OR, IMPLIES, IFF,
      FORALL, EXISTS, UNIQUE, FORALL2, LAM
    };
    enum class VarTag: unsigned char {
      BOUND = 0, FREE, UNDETERMINED
    };
    using enum Tag;
    using enum VarTag;

    Tag tag;
    Expr* s = nullptr; // Next sibling (for children of VAR nodes only)
    string bv = "";    // Bound variable name (for binder nodes only)
    union {
      // VAR (`id` stands for context index for free variables, de Brujin index for bound variables)
      struct { VarTag vartag; unsigned int id; Expr* c; } var;
      // TRUE, FALSE, NOT, AND, OR, IMPLIES, IFF (`l` is ignored for the first two; `r` is ignored for the first three)
      struct { Expr* l, * r; } conn;
      // FORALL, EXISTS, UNIQUE, FORALL2, LAM (`arity` and `sort` must be 0 and SVAR for the first three and the last one)
      struct { unsigned short arity; Sort sort; Expr* r; } binder;
    };

    // The constructors below guarantee that all nonzero pointers in the "active variant" are valid
    Expr(): tag(EMPTY) {}
    Expr(VarTag vartag, unsigned int id, const vector<Expr*>& c = {}): tag(VAR) {
      var.vartag = vartag; var.id = id; attachChildren(c);
    }
    Expr(Tag tag): tag(tag) {
      switch (tag) {
        case TRUE: case FALSE:
          conn.l = conn.r = nullptr; return;
        default: throw new NotImplemented();
      }
    }
    Expr(Tag tag, Expr* l): tag(tag) {
      switch (tag) {
        case NOT:
          conn.l = l; conn.r = nullptr; return;
        default: throw new NotImplemented();
      }
    }
    Expr(Tag tag, Expr* l, Expr* r): tag(tag) {
      switch (tag) {
        case AND: case OR: case IMPLIES: case IFF:
          conn.l = l; conn.r = r; return;
        default: throw new NotImplemented();
      }
    }
    Expr(Tag tag, const string& bv, unsigned short arity, Sort sort, Expr* r): tag(tag) {
      switch (tag) {
        case FORALL: case EXISTS: case UNIQUE: case FORALL2: case LAM:
          this->bv = bv; binder.arity = arity; binder.sort = sort; binder.r = r; return;
        default: throw new NotImplemented();
      }
    }
    // Assignment is shallow copy
    Expr(const Expr&) = default;
    Expr& operator=(const Expr&) = default;

    // Deep copy
    // Pre: all nonzero pointers are valid
    // O(size)
    Expr* clone(Allocator<Expr>& pool) const;

    // Attach children (no-copy)
    // Each node may only be attached to **one** parent node at a time!
    void attachChildren(const vector<Expr*>& nodes) noexcept;

    // Syntactical equality and hash code (up to alpha-renaming!)
    // Pre: { `this`, `rhs` } is arity-consistent
    // O(size)
    bool operator==(const Expr& rhs) const noexcept;
    bool operator!=(const Expr& rhs) const noexcept { return !(*this == rhs); }
    size_t hash() const noexcept;

    // Print
    // Pre: all nonzero pointers are valid
    // `stk` will be unchanged
    // O(size)
    string toString(const Context& ctx, vector<pair<Type, string>>& stk) const;
    string toString(const Context& ctx) const { vector<pair<Type, string>> stk; return toString(ctx, stk); }

    // Check if the subtree is well-formed, and return its type
    // Throws exception on failure
    // Pre: all nonzero pointers are valid
    // `stk` will be unchanged
    // O(size)
    Type checkType(const Context& ctx, vector<Type>& stk) const;
    Type checkType(const Context& ctx) const { vector<Type> stk; return checkType(ctx, stk); }

    // Check if given variable is in the subtree
    // Pre: all nonzero pointers are valid
    bool occurs(VarTag vartag, unsigned int id) const noexcept;

    // Check if the formula does not contain undetermined variables
    bool isGround() const noexcept;

    // Modification (deep copying whole expression)
    // Pre: all nonzero pointers are valid
    // n = (number of binders on top of current node)
    template <typename F>
    Expr* updateVars(unsigned int n, Allocator<Expr>& pool, const F& f) const {
      // First shallow copy to pool
      Expr* res = pool.pushBack(*this);
      using enum Tag;
      switch (tag) {
        case EMPTY: return res;
        case VAR: {
          // Modify subexpressions
          Expr* last = nullptr;
          for (const Expr* p = var.c; p; p = p->s) {
            Expr* q = p->updateVars(n, pool, f);
            (last? last->s : res->var.c) = q;
            last = q;
          }
          (last? last->s : res->var.c) = nullptr;
          // Apply f on the newly created node and return
          return f(n, res);
        }
        case TRUE: case FALSE:
          return res;
        case NOT:
          if (conn.l) res->conn.l = conn.l->updateVars(n, pool, f);
          return res;
        case AND: case OR: case IMPLIES: case IFF:
          if (conn.l) res->conn.l = conn.l->updateVars(n, pool, f);
          if (conn.r) res->conn.r = conn.r->updateVars(n, pool, f);
          return res;
        case FORALL: case EXISTS: case UNIQUE: case FORALL2: case LAM:
          if (binder.r) res->binder.r = binder.r->updateVars(n + 1, pool, f);
          return res;
      }
      throw NotImplemented();
    }

    // Make a free variable into an overflow variable (deep copying whole expression)
    Expr* makeBound(unsigned int id, Allocator<Expr>& pool) const {
      return updateVars(0, pool, [id] (unsigned int n, Expr* x) {
        if (x->var.vartag == FREE && x->var.id == id) { x->var.vartag = BOUND; x->var.id = n; }
        return x;
      });
    }

    // Replace one overflow variable by an expression (deep copying whole expression)
    Expr* makeReplace(const Expr* t, Allocator<Expr>& pool) const {
      return updateVars(0, pool, [t, &pool] (unsigned int n, Expr* x) {
        if (x->var.vartag == BOUND && x->var.id == n) return t->clone(pool);
        return x;
      });
    }

    // Prepare to insert k binders around a subexpression with overflow variables (deep copying whole expression)
    Expr* makeGap(unsigned int k, Allocator<Expr>& pool) const {
      return updateVars(0, pool, [k] (unsigned int n, Expr* x) {
        if (x->var.vartag == BOUND && x->var.id >= n) x->var.id += k;
        return x;
      });
    }

    // Skip through lambda binders
    // Pre: expression must be arity-consistent
    pair<unsigned int, const Expr*> getBody() const noexcept {
      unsigned int res = 0;
      const Expr* p = this;
      while (p->tag == LAM) p = p->binder.r, res++;
      return { res, p };
    }

    // Replace k overflow variables simultaneously, with t's possibly containing overflow variables...
    // (Deep copying whole expression)
    // Pre: ts.size() >= "maximum index overflow" (x->var.id - n + 1)
    Expr* makeReplaceK(vector<const Expr*> ts, Allocator<Expr>& pool) const {
      std::reverse(ts.begin(), ts.end()); // Leftmost arguments are used to substitute highest lambdas
      return updateVars(0, pool, [&ts, &pool] (unsigned int n, Expr* x) {
        if (x->var.vartag == BOUND && x->var.id >= n) return ts[x->var.id - n]->makeGap(n, pool);
        return x;
      });
    }

    // Substitute in a lambda function (deep copying whole expression).
    // Pre: the 2nd argument is a lambda function/predicate with k lambda binders
    // Pre: in the 3rd argument, all applications of the "overflow-bound" function/predicate must have k arguments
    // To ensure that the resulting expression is well-formed, functions must be replaced by functions and
    // predicates must be replaced by predicates (i.e. types must match)
    Expr* makeReplaceLam(const Expr* lam, Allocator<Expr>& pool) const {
      auto [k, body] = lam->getBody();
      return updateVars(0, pool, [k, body, &pool] (unsigned int n, Expr* x) {
        if (x->var.vartag == BOUND && x->var.id == n) {
          vector<const Expr*> args;
          for (const Expr* p = x->var.c; p; p = p->s) args.push_back(p);
          if (k != args.size()) throw Unreachable();
          return body->makeReplaceK(args, pool);
        }
        return x;
      });
    }

    // TODO: pretty print (infixl, infixr, precedence, etc.)

    template <typename ...Ts>
    inline static Expr* make(Allocator<Expr>& pool, const Ts&... args) {
      return pool.pushBack(Expr(args...));
    }
  };

  // An exception class representing checking failure
  struct InvalidExpr: public CheckFailure {
    InvalidExpr(const string& s, const Context& ctx, const Expr* e): CheckFailure("Invalid expression, " + s + ": " + e->toString(ctx)) {}
  };

}

#endif // EXPR_HPP_
