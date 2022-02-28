#include <iostream>
#include <string>
#include <initializer_list>
#include "core.hpp"
#include "elab/tableau.hpp"
#include "elab/procs.hpp"

using std::string;
using std::cin, std::cout, std::endl;
using namespace Core;


// TODO: read text & binary files

int main() {
  using enum Expr::Tag;

  cout << sizeof(string) << endl;
  cout << sizeof(Expr) << endl;
  cout << sizeof(Proof) << endl;
  cout << sizeof(Decl) << endl;

  #define N(...) Expr::make(pool, __VA_ARGS__)

  #define fv(id, ...) N(FREE,  id, std::initializer_list<Expr*>{__VA_ARGS__})
  #define bv(id, ...) N(BOUND, id, std::initializer_list<Expr*>{__VA_ARGS__})

  #define T                   N(TRUE)
  #define F                   N(FALSE)
  #define un(tag, a)          N(tag, a)
  #define bin(a, tag, b)      N(tag, a, b)
  #define forall(s, a)        N(FORALL, s, 0, SVAR, a)
  #define exists(s, a)        N(EXISTS, s, 0, SVAR, a)
  #define unique(s, a)        N(UNIQUE, s, 0, SVAR, a)
  #define forallpred(s, k, a) N(FORALL2, s, k, SPROP, a)
  #define forallfunc(s, k, a) N(FORALL2, s, k, SVAR, a)
  #define lam(s, a)           N(LAM, s, 0, SVAR, a)

  {
    Context ctx;
    Allocator<Expr> pool;

    unsigned int eq = ctx.eq;
    unsigned int in = ctx.addDef("in", {{ 2, SPROP }});

    // The axiom schema of separation...
    Expr* x = forallpred("phi", 2, forall("x", exists("y", forall("a", bin(fv(in, bv(0), bv(1)), IFF, bin(fv(in, bv(0), bv(2)), AND, bv(3, bv(2), bv(0))))))));

    cout << x->toString(ctx) << endl;
    cout << showType(x->checkType(ctx)) << endl;

    unsigned int subset = ctx.addDef("subset", {{ 2, SPROP }, { 1, SVAR }});
    unsigned int issc = ctx.addDef("is_subclass", {{ 1, SPROP }, { 1, SPROP }, { 0, SPROP }});

    Expr* y = lam("x", fv(subset, lam("y", lam("z", T)), bv(0)));

    cout << y->toString(ctx) << endl;
    cout << showType(y->checkType(ctx)) << endl;

    Expr* z = fv(issc, lam("x", F), lam("x", T));

    cout << z->toString(ctx) << endl;
    cout << showType(z->checkType(ctx)) << endl;

    cout << (*x == *y) << (*y == *z) << (*z == *x) << endl;
    cout << (*x == *x) << (*y == *y) << (*z == *z) << endl;

    Expr* x1 = x->clone(pool);
    Expr* xrep = x->binder.r->makeReplaceLam(lam("x", lam("y", fv(eq, bv(1), bv(0)))), pool);

    cout << (*x == *x1) << endl;
    cout << xrep->toString(ctx) << endl;
    cout << showType(xrep->checkType(ctx)) << endl;
  }

  {
    Context ctx;
    Allocator<Expr> pool;
    Allocator<Proof> ps;
    Allocator<Decl> ds;

    #define block std::initializer_list<Decl*>

    unsigned int eq = ctx.eq;
    unsigned int i = ctx.size();

    Decl* d =
      Decl::make(ds, block{
        Decl::make(ds, "p", 0, SPROP), // +0
        Decl::make(ds, "h1", un(NOT, bin(fv(i + 0), OR, un(NOT, fv(i + 0))))), // +1
        Decl::make(ds, "h2", fv(i + 0)), // +2
        Decl::make(ds, "t1", bin(fv(i + 0), OR, un(NOT, fv(i + 0))),
                   Proof::make(ps, Proof::OR_L, Proof::make(ps, i + 2), Proof::make(ps, un(NOT, fv(i + 0))))), // +3
        Decl::make(ds, "t2", nullptr /* false */,
                   Proof::make(ps, Proof::NOT_E, Proof::make(ps, i + 1), Proof::make(ps, i + 3))), // +4
        Decl::make(ds, Decl::POP),
        // +0: p : SPROP
        // +1: (not (p or not p))
        // +2: (p -> (p or not p))
        // +3: (p -> false)
        Decl::make(ds, "t3", un(NOT, fv(i + 0)),
                   Proof::make(ps, Proof::NOT_I, Proof::make(ps, i + 3))), // +4
        Decl::make(ds, "t4", nullptr /* p or not p */,
                   Proof::make(ps, Proof::OR_R, Proof::make(ps, fv(i + 0)), Proof::make(ps, i + 4))), // +5
        Decl::make(ds, "t5", F,
                   Proof::make(ps, Proof::NOT_E, Proof::make(ps, i + 1), Proof::make(ps, i + 5))), // +6
        Decl::make(ds, Decl::POP),
        // +0: p : SPROP
        // +1: (not (p or not p) -> p -> (p or not p))
        // +2: (not (p or not p) -> p -> false)
        // +3: (not (p or not p) -> not p)
        // +4: (not (p or not p) -> (p or not p))
        // +5: (not (p or not p) -> false)
        Decl::make(ds, "t6", nullptr /* p or not p*/,
                   Proof::make(ps, Proof::RAA, Proof::make(ps, i + 5))), // +6
        Decl::make(ds, Decl::POP),
        // +0: (forallpred p/0, not (p or not p) -> p -> (p or not p))
        // +1: (forallpred p/0, not (p or not p) -> p -> false)
        // +2: (forallpred p/0, not (p or not p) -> not p)
        // +3: (forallpred p/0, not (p or not p) -> (p or not p))
        // +4: (forallpred p/0, not (p or not p) -> false)
        // +5: (forallpred p/0, p or not p)
      });

    d->check(ctx, pool);

    Decl* d1 =
      Decl::make(ds, block{
        Decl::make(ds, "x", 0, SVAR), // +6
        Decl::make(ds, "y", 0, SVAR), // +7
        Decl::make(ds, "t7", nullptr /* x = y or not x = y */,
                   Proof::make(ps, Proof::FORALL2_E, Proof::make(ps, i + 5), Proof::make(ps, fv(eq, fv(i + 6), fv(i + 7))))), // +8
        Decl::make(ds, Decl::POP),
        Decl::make(ds, Decl::POP),
        // +6: (forall x y, x = y not x = y)
      });

    d1->check(ctx, pool);

    Decl* d2 =
      Decl::make(ds, block{
        Decl::make(ds, "q", 2, SPROP), // +7
        Decl::make(ds, "x", 0, SVAR), // +8
        Decl::make(ds, "y", 0, SVAR), // +9
        Decl::make(ds, "t8", bin(fv(i + 7, fv(i + 8), fv(i + 9)), OR, un(NOT, fv(i + 7, fv(i + 8), fv(i + 9)))),
                   Proof::make(ps, Proof::FORALL2_E, Proof::make(ps, i + 5), Proof::make(ps, fv(i + 7, fv(i + 8), fv(i + 9))))), // +10
        Decl::make(ds, Decl::POP),
        Decl::make(ds, Decl::POP),
        Decl::make(ds, Decl::POP),
        // +7: (forallpred q/2, forall x y, q x y or not q x y)
      });

    d2->check(ctx, pool);

    for (size_t i = 0; i < ctx.size(); i++) {
      cout << ctx.nameOf(i) << ": ";
      if (holds_alternative<Type>(ctx[i])) cout << showType(get<Type>(ctx[i])) << endl;
      if (holds_alternative<const Expr*>(ctx[i])) cout << get<const Expr*>(ctx[i])->toString(ctx) << endl;
    }
  }

  {
    Context ctx;
    Allocator<Expr> pool;
    Allocator<Proof> ps;
    Allocator<Decl> ds;

    unsigned int eq = ctx.eq;
    unsigned int i = ctx.size();

    Decl* d =
      Decl::make(ds, block{
        Decl::make(ds, "x", 0, SVAR), // +0
        Decl::make(ds, "y", 0, SVAR), // +1
        Decl::make(ds, Decl::PDEF, "phi", "phi_def",
                   bin(fv(eq, fv(i + 0), fv(i + 1)), AND, fv(eq, fv(i + 1), fv(i + 0)))), // +2, +3
        Decl::make(ds, Decl::POP),
        Decl::make(ds, Decl::POP)
        // +0: phi: SVAR -> SVAR -> SPROP
        // +1: phi_def : (forall x y, phi x y <-> (x = y and y = x))
      });

    d->check(ctx, pool);

    Decl* d1 =
      Decl::make(ds, block{
        Decl::make(ds, "+", 2, SVAR), // +2
        Decl::make(ds, "x", 0, SVAR), // +3
        Decl::make(ds, "y", 0, SVAR), // +4
        Decl::make(ds, "h1", fv(eq, fv(i + 3), fv(i + 4))), // +5
        Decl::make(ds, Decl::FDEF, "f", "f_def",
                   fv(i + 2, fv(i + 3), fv(i + 4))), // +6, +7
        Decl::make(ds, Decl::POP),
        Decl::make(ds, Decl::POP),
        Decl::make(ds, Decl::POP)
        // +2: +: SVAR -> SVAR -> SVAR
        // +3: f: SVAR -> SVAR -> SVAR
        // +4: f_def : (forall x y, x = y -> f x y = x + y)
      });

    d1->check(ctx, pool);

    for (size_t i = 0; i < ctx.size(); i++) {
      cout << ctx.nameOf(i) << ": ";
      if (holds_alternative<Type>(ctx[i])) cout << showType(get<Type>(ctx[i])) << endl;
      if (holds_alternative<const Expr*>(ctx[i])) cout << get<const Expr*>(ctx[i])->toString(ctx) << endl;
    }
    cout << endl;
  }

  {
    using namespace Elab;
    Allocator<Expr> pool;
    Context ctx;
    Tableau tableau;

    // unsigned int eq = ctx.eq;
    unsigned int in = ctx.addDef("in", {{ 2, SPROP }});
    unsigned int p = ctx.pushVar("p", {{ 0, SPROP }});
    unsigned int q = ctx.pushVar("q", {{ 0, SPROP }});
    unsigned int r = ctx.pushVar("r", {{ 0, SPROP }});
    unsigned int s = ctx.pushVar("s", {{ 0, SPROP }});

    Expr* e = forallpred("phi", 2, forall("x", exists("y", forall("a", bin(fv(in, bv(0), bv(1)), IFF, bin(fv(in, bv(0), bv(2)), AND, bv(3, bv(2), bv(0))))))));
    /*
    cout << e->hash() << endl;
    cout << e->binder.r->hash() << endl;
    cout << e->binder.r->binder.r->hash() << endl;
    cout << e->binder.r->binder.r->binder.r->binder.r->hash() << endl;
    cout << e->binder.r->binder.r->binder.r->binder.r->conn.l->hash() << endl;
    */
    e = un(NOT, bin(fv(p), OR, un(NOT, fv(p))));
    /*
    cout << e->hash() << endl;
    cout << e->conn.l->hash() << endl;
    cout << e->conn.l->conn.l->hash() << endl;
    cout << e->conn.l->conn.r->conn.l->hash() << endl;
    */
    tableau.addSuccedent(e);
    cout << "Is \"" << e->toString(ctx) << "\" provable? " << tableau.dfs(0, 0) << endl;
    tableau.clear();

    e = bin(fv(p), OR, un(NOT, fv(p)));
    /*
    cout << e->hash() << endl;
    cout << e->conn.l->hash() << endl;
    cout << e->conn.r->conn.l->hash() << endl;
    */
    tableau.addSuccedent(e);
    cout << "Is \"" << e->toString(ctx) << "\" provable? " << tableau.dfs(0, 0) << endl;
    tableau.clear();

    // ¬(p ↔ ¬p)
    e = un(NOT, bin(fv(p), IFF, un(NOT, fv(p))));
    tableau.addSuccedent(e);
    cout << "Is \"" << e->toString(ctx) << "\" provable? " << tableau.dfs(0, 0) << endl;
    tableau.clear();
    cout << endl;

    cout << "Conversion to negation normal form:" << endl;
    e = bin(bin(fv(p), IFF, fv(q)), IFF, un(NOT, bin(fv(r), IMPLIES, fv(s))));
    Expr* nnf = Elab::Procs::toNNF(e, ctx, pool);
    cout << e->toString(ctx) << endl;
    cout << nnf->toString(ctx) << endl;
    Elab::Procs::foreachValuation({ p, q, r, s }, [&e, &nnf] (const vector<bool>& fvmap) {
      cout << Elab::Procs::propValue(e, fvmap);
      cout << Elab::Procs::propValue(nnf, fvmap);
    });
    cout << endl;
    cout << endl;
  }

  {
    using namespace Elab::Procs;
    Allocator<Expr> pool;
    Context ctx;

    unsigned int eq = ctx.eq;
    unsigned int f = ctx.pushVar("f", {{ 2, SVAR }});
    unsigned int g = ctx.pushVar("g", {{ 2, SVAR }});
    unsigned int h = ctx.pushVar("h", {{ 2, SVAR }});
    unsigned int a = ctx.pushVar("a", TTerm);
    unsigned int b = ctx.pushVar("b", TTerm);
    unsigned int offset = ctx.size();
    unsigned int x = ctx.pushVar("x", TTerm);
    unsigned int y = ctx.pushVar("y", TTerm);
    unsigned int z = ctx.pushVar("z", TTerm);
    unsigned int u = ctx.pushVar("u", TTerm);
    unsigned int v = ctx.pushVar("v", TTerm);

    const Expr* lhs = fv(eq, fv(f, fv(x), fv(g, fv(x), fv(y))), fv(h, fv(z), fv(y)));
    const Expr* rhs = fv(eq, fv(z), fv(h, fv(f, fv(u), fv(v)), fv(f, fv(a), fv(b))));
    const Expr* lhs1 = fv(f, fv(x), fv(y));
    const Expr* rhs1 = fv(f, fv(x), fv(f, fv(x), fv(y)));

    cout << "First-order unification:" << endl;
    cout << lhs1->toString(ctx) << endl;
    cout << rhs1->toString(ctx) << endl;
    cout << unify(offset, {{ lhs1, rhs1 }}, pool).has_value() << endl;
    cout << endl;

    cout << lhs->toString(ctx) << endl;
    cout << rhs->toString(ctx) << endl;
    Subs subs = unify(offset, {{ lhs, rhs }}, pool).value();
    for (size_t i = 0; i < subs.ts.size(); i++) if (subs.ts[i]) {
      cout << Expr(FREE, subs.offset + i).toString(ctx) << " -> " << subs.ts[i]->toString(ctx) << endl;
    }
    cout << applySubs(lhs, subs, pool)->toString(ctx) << endl;
    cout << applySubs(rhs, subs, pool)->toString(ctx) << endl;
    cout << endl;

    cout << "First-order anti-unification:" << endl;
    auto [tmpl, lsub, rsub] = antiunify(ctx.size(), lhs, rhs, pool);
    cout << "Template: " << tmpl->toString(ctx) << endl;
    cout << "LHS substitution:" << endl;
    for (size_t i = 0; i < lsub.ts.size(); i++) if (subs.ts[i]) {
      cout << Expr(FREE, lsub.offset + i).toString(ctx) << " -> " << lsub.ts[i]->toString(ctx) << endl;
    }
    cout << applySubs(lhs, lsub, pool)->toString(ctx) << endl;
    cout << "RHS substitution:" << endl;
    for (size_t i = 0; i < rsub.ts.size(); i++) if (subs.ts[i]) {
      cout << Expr(FREE, rsub.offset + i).toString(ctx) << " -> " << rsub.ts[i]->toString(ctx) << endl;
    }
    cout << applySubs(rhs, rsub, pool)->toString(ctx) << endl;
    cout << endl;
  }

  return 0;
}
