#include "proof.hpp"


namespace Core {

  /*
  Type Proof::checkExpr(const Context& ctx) const {
    switch (tag) {
      case EXPR:
        if (!expr.p) throw InvalidProof("null pointer", ctx, this);
        return expr.p->checkType(ctx);
      default: throw InvalidProof("type mismatch, expected expression", ctx, this);
    }
  }

  Expr* Proof::check(const Context& ctx, Allocator<Expr>& pool) const {

    // Some helper functions for checking subproofs
    // Throws exception on failure
    auto proved = [&ctx, &pool, this] (int i) -> Expr* {
      const Proof* p = subpfs.p[i];
      if (!p) throw InvalidProof("null pointer", ctx, this);
      return p->check(ctx, pool);
    };
    // These may require additional clone() since they return expression pointers pointing to subproof data
    auto wff = [&ctx, &pool, this] (int i) -> const Expr* {
      const Proof* p = subpfs.p[i];
      if (!p) throw InvalidProof("null pointer", ctx, this);
      if (p->checkExpr(ctx) != TFormula) throw InvalidProof("type mismatch, expected formula", ctx, this);
      return p->expr.p;
    };
    auto wft = [&ctx, &pool, this] (int i) -> const Expr* {
      const Proof* p = subpfs.p[i];
      if (!p) throw InvalidProof("null pointer", ctx, this);
      if (p->checkExpr(ctx) != TTerm) throw InvalidProof("type mismatch, expected term", ctx, this);
      return p->expr.p;
    };
    auto exprtype = [&ctx, &pool, this] (int i) -> pair<const Expr*, Type> {
      const Proof* p = subpfs.p[i];
      if (!p) throw InvalidProof("null pointer", ctx, this);
      const Type& t = p->checkExpr(ctx);
      return { p->expr.p, t };
    };

    // Some helper macros that try "pattern matching on" a given node (infix for binary connectives)
    //   *a_ must be a valid & well-formed formula
    //   tag_ must be a constant
    //   l_, r_ and name_ must be new identifiers
    // Local variable x_ is used to prevent evaluating a_ multiple times
    // Throws exception on failure
    #define match0(a_, tag_) { \
      Expr* x_ = a_; \
      if (x_->tag != tag_) throw InvalidProof("incorrect main connective", ctx, this); \
    }
    #define match1(a_, tag_, l_) \
    [[maybe_unused]] Expr* l_; { \
      Expr* x_ = a_; \
      if (x_->tag != tag_) throw InvalidProof("incorrect main connective", ctx, this); \
      if (!x_->conn.l)     throw Unreachable(); \
      l_ = x_->conn.l; \
    }
    #define match2(a_, l_, tag_, r_) \
    [[maybe_unused]] Expr* l_, * r_; { \
      Expr* x_ = a_; \
      if (x_->tag != tag_)            throw InvalidProof("incorrect main connective", ctx, this); \
      if (!x_->conn.l || !x_->conn.r) throw Unreachable(); \
      l_ = x_->conn.l, r_ = x_->conn.r; \
    }
    #define matcheq(a_, l_, r_) Expr* l_, * r_; { \
      Expr* x_ = a_; \
      if (x_->tag != VAR || x_->var.vartag != FREE || x_->var.id != ctx.equals) \
        throw InvalidProof("expected proof of equality", ctx, this); \
      l_ = x_->var.c; r_ = l_->s; \
    }
    #define matchbinder(a_, tag_, name_, r_) \
    [[maybe_unused]] string name_; \
    [[maybe_unused]] Expr* r_; { \
      Expr* x_ = a_; \
      if (x_->tag != tag_) throw InvalidProof("incorrect binder", ctx, this); \
      if (!x_->binder.r)   throw Unreachable(); \
      name_ = x_->bv; \
      r_ = x_->binder.r; \
    }
    #define asserteq(l_, r_) \
      if (*(l_) != *(r_)) throw InvalidProof("subexpressions should be equal", ctx, this)
    #define node0(tag_)           Expr::make(pool, tag_)
    #define node1(tag_, l_)       Expr::make(pool, tag_, l_)
    #define node2(l_, tag_, r_)   Expr::make(pool, tag_, l_, r_)
    #define nodebinder(tag_, name_, r_) \
                                  Expr::make(pool, tag_, name_, 0, SVAR, r_) // This binds term variables only
    #define nodevar(f_, id_, ...) Expr::make(pool, f_, id_, std::initializer_list<Expr*>{__VA_ARGS__})

    switch (tag) {
      case EXPR:  throw InvalidProof("type mismatch, expected proof", ctx, this);
      case THM: {
        if (!ctx.valid(thm.id)) throw InvalidProof("referred theorem not in context", ctx, this);
        auto res = get_if<const Expr*>(&ctx[thm.id]);
        if (!res) throw InvalidProof("referred theorem not in context", ctx, this);
        return (*res)->clone(pool);
      }

      // Introduction & elimination rules here
      // (Manual pattern matching!)
      using enum Expr::Tag;
      using enum Expr::VarTag;

      case AND_I: return node2(proved(0), AND, proved(1));
      case AND_L: { match2(proved(0), p, AND, q); return p; }
      case AND_R: { match2(proved(0), p, AND, q); return q; }
      case OR_L: return node2(proved(0), OR, wff(1)->clone(pool));
      case OR_R: return node2(wff(0)->clone(pool), OR, proved(1));
      case OR_E: { match2(proved(0), p0, OR, q0);
                   match2(proved(1), p1, IMPLIES, r0);
                   match2(proved(2), q1, IMPLIES, r1);
                   asserteq(p0, p1); asserteq(q0, q1); asserteq(r0, r1); return r0; }
      case IMPLIES_E: { match2(proved(0), p, IMPLIES, q); asserteq(p, proved(1)); return q; }
      case NOT_I:     { match2(proved(0), p, IMPLIES, f); match0(f, FALSE); return node1(NOT, p); }
      case NOT_E:     { match1(proved(0), NOT, p); asserteq(p, proved(1)); return node0(FALSE); }
      case IFF_I:     { match2(proved(0), p0, IMPLIES, q0); match2(proved(1), q1, IMPLIES, p1);
                        asserteq(p0, p1); asserteq(q0, q1); return node2(p0, IFF, q0); }
      case IFF_L: { match2(proved(0), p, IFF, q); asserteq(p, proved(1)); return q; }
      case IFF_R: { match2(proved(0), p, IFF, q); asserteq(q, proved(1)); return p; }
      case TRUE_I: return node0(TRUE);
      case FALSE_E: { match0(proved(0), FALSE); return wff(1)->clone(pool); }
      case RAA: { match2(proved(0), np, IMPLIES, f); match1(np, NOT, p); match0(f, FALSE); return p; }
      case EQUALS_I: {
        const Expr* t = wft(0);
        return nodevar(FREE, ctx.equals, t->clone(pool), t->clone(pool));
      }
      case EQUALS_E: {
        auto [p, type] = exprtype(0);
        if (!(p->tag == LAMBDA && type == Type{{ 1, SPROP }}))
          throw InvalidProof("type mismatch, expected unary predicate", ctx, this);
        Expr* px = p->binder.r, * pa = proved(2);
        matcheq(proved(1), a, b);
        asserteq(px->makeReplace(a, pool), pa);
        return px->makeReplace(b, pool);
      }
      case FORALL_E: {
        matchbinder(proved(0), FORALL, x, px);
        return px->makeReplace(wft(1), pool);
      }
      case EXISTS_I: {
        Expr* conc = wff(0)->clone(pool);
        matchbinder(conc, EXISTS, x, px);
        asserteq(px->makeReplace(wft(1), pool), proved(2));
        return conc;
      }
      case EXISTS_E: {
        matchbinder(proved(0), EXISTS, x0, px0);
        matchbinder(proved(1), FORALL, x1, px1q);
        match2(px1q, px1, IMPLIES, q);
        asserteq(px0, px1); asserteq(q, wff(2));
        return q;
      }
      case UNIQUE_I: {
        matchbinder(proved(0), EXISTS, x0, px0);
        matchbinder(proved(1), FORALL, x1, a); match2(a, px1, IMPLIES, b);
        matchbinder(b,         FORALL, x2, c); match2(c, px2, IMPLIES, d);
        matcheq(d, l, r);
        if (!(l->tag == VAR && l->var.vartag == BOUND && l->var.id == 1 &&
              r->tag == VAR && r->var.vartag == BOUND && r->var.id == 0))
          throw InvalidProof("expected proof of uniqueness", ctx, this);
        asserteq(px0, px1); asserteq(px0, px2);
        return nodebinder(UNIQUE, x0, px0);
      }
      case UNIQUE_L: {
        matchbinder(proved(0), UNIQUE, x, px);
        return nodebinder(EXISTS, x, px);
      }
      case UNIQUE_R: {
        matchbinder(proved(0), UNIQUE, x, px);
        return nodebinder(FORALL, x,       node2(px, IMPLIES,
               nodebinder(FORALL, x + "'", node2(px->clone(pool), IMPLIES,
                          nodevar(FREE, ctx.equals, nodevar(BOUND, 1), nodevar(BOUND, 0))))));
      }
      case FORALL2_E: {
        // Check LHS
        Expr* p = proved(0);
        if (p->tag != FORALL2) throw InvalidProof("incorrect binder", ctx, this);
        if (!p->binder.r) throw InvalidProof("null pointer", ctx, this);
        unsigned short k = p->binder.arity;
        Sort s = p->binder.sort;
        Expr* q = p->binder.r;
        // Check RHS
        auto [f, type] = exprtype(1);
        if (type != Type{{ k, s }}) throw InvalidProof("arity or target sort mismatch", ctx, this);
        // Apply and return
        return q->makeReplaceLam(f, pool);
      }
    }

    #undef match0
    #undef match1
    #undef match2
    #undef matcheq
    #undef matchbinder
    #undef asserteq
    #undef node0
    #undef node1
    #undef node2
    #undef nodebinder
    #undef nodevar
    throw NotImplemented();
  }

  */

  void Decl::attachChildren(const vector<Decl*>& nodes) {
    if (tag != BLOCK) return;
    Decl* last = nullptr;
    for (Decl* node: nodes) {
      (last? last->s : block.c) = node;
      last = node;
    }
    (last? last->s : block.c) = nullptr;
  }

  void Decl::check(Context& ctx, Allocator<Expr>& pool) const {

    auto proved = [&ctx, &pool, this] (const Proof* p) -> Expr* {
      if (!p) throw InvalidDecl("null pointer", ctx, this);
      return p->check(ctx, pool);
    };
    auto wff = [&ctx, this] (const Expr* p) -> const Expr* {
      if (!p) throw InvalidDecl("null pointer", ctx, this);
      if (p->checkType(ctx) != TFormula) throw InvalidDecl("type mismatch, expected formula", ctx, this);
      return p;
    };
    auto wft = [&ctx, this] (const Expr* p) -> const Expr* {
      if (!p) throw InvalidDecl("null pointer", ctx, this);
      if (p->checkType(ctx) != TTerm) throw InvalidDecl("type mismatch, expected term", ctx, this);
      return p;
    };

    #define matchbinder(a_, tag_, name_, r_) \
    [[maybe_unused]] string name_; \
    [[maybe_unused]] Expr* r_; { \
      Expr* x_ = a_; \
      if (x_->tag != tag_) throw InvalidDecl("incorrect binder", ctx, this); \
      if (!x_->binder.r)   throw Unreachable(); \
      name_ = x_->bv; \
      r_ = x_->binder.r; \
    }
    #define node2(l_, tag_, r_)   Expr::make(pool, tag_, l_, r_)
    #define nodebinder(tag_, name_, r_) \
                                  Expr::make(pool, tag_, name_, 0, SVAR, r_) // This binds term variables only
    #define nodevar(f_, id_, ...) Expr::make(pool, f_, id_, std::initializer_list<Expr*>{__VA_ARGS__})

    switch (tag) {
      case BLOCK:
        for (const Decl* p = block.c; p; p = p->s) p->check(ctx, pool);
        return;
      case ASSERTION: {
        const Expr* res = proved(assertion.pf);
        if (assertion.e && *res != *(assertion.e))
          throw InvalidDecl("invalid assertion - statement and proof do not match", ctx, this);
        ctx.addTheorem(name, assertion.e? assertion.e->clone(pool) : res);
        return;
      }
      case ASSUME: ctx.pushAssumption(name, wff(assume.e)->clone(pool)); return;
      case ANY:    ctx.pushVar(name, Type{{ any.arity, any.sort }}); return;
      case POP:    if (!ctx.pop(pool)) throw InvalidDecl("error popping - assumption stack is empty at this point", ctx, this); return;

      // Definition rules here
      using enum Expr::Tag;
      using enum Expr::VarTag;

      case FDEF: {
        unsigned int id = ctx.addDef(name, TTerm);
        ctx.addTheorem(namedef, nodevar(FREE, ctx.equals, nodevar(FREE, id), wft(fdef.e)->clone(pool)));
        return;
      }
      case PDEF: {
        unsigned int id = ctx.addDef(name, TFormula);
        ctx.addTheorem(namedef, node2(nodevar(FREE, id), IFF, wff(pdef.e)->clone(pool)));
        return;
      }
      case DDEF: {
        matchbinder(proved(ddef.pf), UNIQUE, x, px);
        unsigned int id = ctx.addDef(name, TTerm);
        ctx.addTheorem(namedef, nodebinder(FORALL, x, node2(px, IFF, nodevar(FREE, ctx.equals, nodevar(BOUND, 0), nodevar(FREE, id)))));
        return;
      }
      case IDEF: {
        matchbinder(proved(idef.pf), EXISTS, x, px);
        unsigned int id = ctx.addDef(name, TTerm);
        ctx.addTheorem(namedef, px->makeReplace(nodevar(FREE, id), pool));
        return;
      }
      case UNDEF: {
        throw NotImplemented();
      }
    }

    #undef matchbinder
    #undef node2
    #undef nodebinder
    #undef nodevar
    throw NotImplemented();
  }

}
