#ifndef PROOF_HPP_
#define PROOF_HPP_

#include "base.hpp"
#include "context.hpp"
#include "expr.hpp"


namespace Core {

  // Derivation trees (aka. proof terms)
  class Proof {
  public:
    enum Rule: unsigned char {
      EMPTY = 0,
      EXPR, THM,
      AND_I, AND_L, AND_R, OR_L, OR_R, OR_E, IMPLIES_E, NOT_I, NOT_E, IFF_I, IFF_L, IFF_R, TRUE_I, FALSE_E, RAA,
      EQ_I, EQ_E, FORALL_E, EXISTS_I, EXISTS_E, UNIQUE_I, UNIQUE_L, UNIQUE_R, FORALL2_E
    } rule;

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
    Proof(Rule rule): rule(rule) {
      switch (rule) {
        case EMPTY: break;
        case EXPR: expr.p = nullptr; break;
        default: subpfs.p[0] = subpfs.p[1] = subpfs.p[2] = nullptr; break;
      }
    }
    // Assignment is shallow copy
    Proof(const Proof&) = default;
    Proof& operator=(const Proof&) = default;
    // Some convenient constructors
    // TODO: check rule
    Proof(const Expr* e): rule(EXPR) { expr.p = e; }
    Proof(unsigned int id): rule(THM) { thm.id = id; }
    Proof(Rule r, Proof* p0): rule(r) { subpfs.p[0] = p0; subpfs.p[1] = subpfs.p[2] = nullptr; }
    Proof(Rule r, Proof* p0, Proof* p1): rule(r) { subpfs.p[0] = p0; subpfs.p[1] = p1; subpfs.p[2] = nullptr; }
    Proof(Rule r, Proof* p0, Proof* p1, Proof* p2): rule(r) { subpfs.p[0] = p0; subpfs.p[1] = p1; subpfs.p[2] = p2; }

    // TODO: debug output

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


  class Decl {
  public:
    enum Category: unsigned char {
      EMPTY = 0,
      BLOCK, ASSERTION,
      ASSUME, ANY, POP,
      FDEF, PDEF, DDEF, IDEF, UNDEF
    } category;

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
    Decl(Category cat): category(cat) {
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
    // Assignment is shallow copy
    Decl(const Decl&) = default;
    Decl& operator=(const Decl&) = default;
    // Some convenient constructors
    // TODO: check category
    Decl(const std::initializer_list<Decl*>& c): category(BLOCK) { attachChildren(c); }
    Decl(string name, const Expr* e, const Proof* pf): category(ASSERTION), name(name) { assertion.e = e; assertion.pf = pf; }
    Decl(Category cat, string name, string namedef, const Proof* pf): category(cat), name(name), namedef(namedef) {
      switch (category) {
        case DDEF: ddef.pf = pf; break;
        case IDEF: idef.pf = pf; break;
        default: throw Unreachable();
      }
    }
    Decl(Category cat, string name, string namedef, const Expr* e): category(cat), name(name), namedef(namedef) {
      switch (category) {
        case FDEF: fdef.e = e; break;
        case PDEF: pdef.e = e; break;
        default: throw Unreachable();
      }
    }
    Decl(string name, const Expr* e): category(ASSUME), name(name) { assume.e = e; }
    Decl(string name, unsigned short arity, Sort sort): category(ANY), name(name) { any.arity = arity; any.sort = sort; }

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
