// Core :: Proof, Decl, InvalidProof, InvalidDecl

#ifndef PROOF_HPP_
#define PROOF_HPP_

#include "base.hpp"
#include "context.hpp"
#include "expr.hpp"


namespace Core {

  // Derivation trees (aka. proof terms)
  class Proof {
  public:
    enum class Rule: unsigned char {
      EMPTY = 0,
      EXPR, THM,
      AND_I, AND_L, AND_R, OR_L, OR_R, OR_E, IMPLIES_E, NOT_I, NOT_E, IFF_I, IFF_L, IFF_R, TRUE_I, FALSE_E, RAA,
      EQ_I, EQ_E, FORALL_E, EXISTS_I, EXISTS_E, UNIQUE_I, UNIQUE_L, UNIQUE_R, FORALL2_E
    };
    using enum Rule;

    Rule rule = EMPTY;
    // Since most rules have less or equal than 3 child proofs, I guess I could save writing some boilerplate code
    // for a discriminated union...
    // Unlike expressions, DAGs are allowed for proofs: each node may be attached to multiple parent nodes at a time.
    // Unused fields/pointers are ignored (will not be checked).
    union {
      struct { const Expr* p; } expr;
      struct { unsigned int id; } thm;
      struct { const Proof* p[3]; } subpfs;
    };

    // The constructors below guarantee that all nonzero pointers (in the "active variant") are valid
    Proof(): rule(EMPTY) {}
    Proof(Rule rule, Proof* p0 = nullptr, Proof* p1 = nullptr, Proof* p2 = nullptr): rule(rule) {
      switch (rule) {
        case EMPTY: break;
        case EXPR: expr.p = nullptr; break;
        default: subpfs.p[0] = p0; subpfs.p[1] = p1; subpfs.p[2] = p2; break;
      }
    }
    Proof(const Expr* e): rule(EXPR) { expr.p = e; }
    Proof(unsigned int id): rule(THM) { thm.id = id; }
    // Assignment is shallow copy
    Proof(const Proof&) = default;
    Proof& operator=(const Proof&) = default;

    // TODO: debug output

    // Checks well-formedness (rule must be `EXPR`)
    Type checkExpr(const Context& ctx) const;

    // Checks proof (currently no side-effects on `ctx`)
    // Returned pointer is valid & points to a well-formed formula
    Expr* check(const Context& ctx, Allocator<Expr>& pool) const;
  };

  template<typename ...Ts>
  inline Proof* newProof(Allocator<Proof>& pool, const Ts&... args) {
    return pool.pushBack(Proof(args...));
  }

  // An exception class representing checking failure
  struct InvalidProof: public CheckFailure {
    InvalidProof(const string& s, const Context&, const Proof*): CheckFailure("Invalid proof, " + s) {}
  };


  // Pre (for all methods): there is no "cycle" throughout the tree
  // Pre & invariant (for all methods): all nonzero pointers (in the "active variant") are valid
  class Decl {
  public:
    enum class Category: unsigned char {
      EMPTY = 0,
      BLOCK, ASSERTION,
      ASSUME, ANY, POP,
      FDEF, PDEF, DDEF, IDEF, UNDEF
    };
    using enum Category;

    Category category = EMPTY;
    Decl* s = nullptr; // Next sibling
    // Non-POD class instance cannot be stored inside unions
    // (or I will have to manually call their constructors & destructors)
    string name = "", namedef = "";
    union {
      struct { Decl* c; } block;
      struct { const Expr* e; const Proof* pf; } assertion;
      struct { const Proof* pf; } ddef, idef;
      struct { const Expr* e; } assume, fdef, pdef;
      struct { unsigned short arity; Sort sort; } any;
    };

    // The constructors below guarantee that all nonzero pointers (in the "active variant") are valid
    Decl(): category(EMPTY) {}
    Decl(Category cat, const string& name = "", const string& namedef = ""):
         category(cat), name(name), namedef(namedef) {
      switch (category) {
        case EMPTY: case ANY: case POP: case UNDEF: break;
        case BLOCK: block.c = nullptr; break;
        case ASSERTION: assertion.e = nullptr; assertion.pf = nullptr; break;
        case ASSUME: assume.e = nullptr; break;
        case FDEF: fdef.e = nullptr; break;
        case PDEF: pdef.e = nullptr; break;
        case DDEF: ddef.pf = nullptr; break;
        case IDEF: idef.pf = nullptr; break;
      }
    }
    Decl(const std::initializer_list<Decl*>& c): category(BLOCK) { attachChildren(c); }
    Decl(const string& name, const Expr* e, const Proof* pf): category(ASSERTION), name(name) { assertion.e = e; assertion.pf = pf; }
    Decl(const string& name, const Expr* e): category(ASSUME), name(name) { assume.e = e; }
    Decl(const string& name, unsigned short arity, Sort sort): category(ANY), name(name) { any.arity = arity; any.sort = sort; }
    Decl(Category cat, const string& name, const string& namedef, const Expr* e): Decl(cat, name, namedef) {
      if (category == FDEF) fdef.e = e;
      if (category == PDEF) pdef.e = e;
    }
    Decl(Category cat, const string& name, const string& namedef, const Proof* pf): Decl(cat, name, namedef) {
      if (category == DDEF) ddef.pf = pf;
      if (category == IDEF) idef.pf = pf;
    }
    // Assignment is shallow copy
    Decl(const Decl&) = default;
    Decl& operator=(const Decl&) = default;

    // TODO: debug output

    // Attach children (no-copy)
    // Each node may only be attached to **one** parent node at a time!
    // Pre: category is BLOCK
    void attachChildren(const std::initializer_list<Decl*>& nodes);

    // Checks declarations, side-effecting the context `ctx` (newly created expressions will be stored in `pool`)
    // Throws exception on failure
    void check(Context& ctx, Allocator<Expr>& pool) const;
  };

  template<typename ...Ts>
  inline Decl* newDecl(Allocator<Decl>& pool, const Ts&... args) {
    return pool.pushBack(Decl(args...));
  }

  // An exception class representing checking failure
  struct InvalidDecl: public CheckFailure {
    InvalidDecl(const string& s, const Context&, const Decl*): CheckFailure("Invalid expression, " + s) {}
  };

}

#endif // PROOF_HPP_
