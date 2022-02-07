#include <iostream>
#include <string>
#include <initializer_list>
#include "core.hpp"

using std::string;
using std::cin, std::cout, std::endl;
using namespace Core;


// TODO: read text & binary files

int main() {
  using enum Expr::Symbol;

  cout << sizeof(string) << endl;
  cout << sizeof(Expr) << endl;
  cout << sizeof(Proof) << endl;
  cout << sizeof(Decl) << endl;

  #define N(...) newNode(pool, __VA_ARGS__)

  #define fv(id, ...) N(FREE,  id, std::initializer_list<Expr*>{__VA_ARGS__})
  #define bv(id, ...) N(BOUND, id, std::initializer_list<Expr*>{__VA_ARGS__})

  #define T                 N(TRUE)
  #define F                 N(FALSE)
  #define un(sym, a)        N(sym, a)
  #define bin(a, sym, b)    N(sym, a, b)
  #define forall(a)         N(FORALL, 0, SVAR, a)
  #define exists(a)         N(EXISTS, 0, SVAR, a)
  #define unique(a)         N(UNIQUE, 0, SVAR, a)
  #define forallpred(k, a)  N(FORALL2, k, SPROP, a)
  #define forallfunc(k, a)  N(FORALL2, k, SVAR, a)
  #define lam(a)            N(LAM, 0, SVAR, a)

  {
    Context ctx;
    Allocator<Expr> pool;

    unsigned int eq = ctx.eq;
    unsigned int in = ctx.addDef("in", {{ 2, SPROP }});

    // The axiom schema of separation...
    Expr* x = forallpred(2, forall(exists(forall(bin(fv(in, bv(0), bv(1)), IFF, bin(fv(in, bv(0), bv(2)), AND, bv(3, bv(2), bv(0))))))));

    cout << x->toString(ctx) << endl;
    cout << showType(x->checkType(ctx)) << endl;

    unsigned int subset = ctx.addDef("subset", {{ 2, SPROP }, { 1, SVAR }});
    unsigned int issc = ctx.addDef("is_subclass", {{ 1, SPROP }, { 1, SPROP }, { 0, SPROP }});

    Expr* y = lam(fv(subset, lam(lam(T)), bv(0)));

    cout << y->toString(ctx) << endl;
    cout << showType(y->checkType(ctx)) << endl;

    Expr* z = fv(issc, lam(F), lam(T));

    cout << z->toString(ctx) << endl;
    cout << showType(z->checkType(ctx)) << endl;

    cout << (*x == *y) << (*y == *z) << (*z == *x) << endl;
    cout << (*x == *x) << (*y == *y) << (*z == *z) << endl;

    Expr* x1 = x->clone(pool);
    Expr* xrep = x->binder.r->makeReplaceLam(lam(lam(fv(eq, bv(1), bv(0)))), pool);

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
    unsigned int i = ctx.nextIndex();

    Decl* d =
      newDecl(ds, block{
        newDecl(ds, "p", 0, SPROP), // +0
        newDecl(ds, "h1", un(NOT, bin(fv(i + 0), OR, un(NOT, fv(i + 0))))), // +1
        newDecl(ds, "h2", fv(i + 0)), // +2
        newDecl(ds, "t1", bin(fv(i + 0), OR, un(NOT, fv(i + 0))),
                    newProof(ps, Proof::OR_L, newProof(ps, i + 2), newProof(ps, un(NOT, fv(i + 0))))), // +3
        newDecl(ds, "t2", nullptr /* false */,
                    newProof(ps, Proof::NOT_E, newProof(ps, i + 1), newProof(ps, i + 3))), // +4
        newDecl(ds, Decl::POP),
        // +0: p : SPROP
        // +1: (not (p or not p))
        // +2: (p -> (p or not p))
        // +3: (p -> false)
        newDecl(ds, "t3", un(NOT, fv(i + 0)), 
                    newProof(ps, Proof::NOT_I, newProof(ps, i + 3))), // +4
        newDecl(ds, "t4", nullptr /* p or not p */,
                    newProof(ps, Proof::OR_R, newProof(ps, fv(i + 0)), newProof(ps, i + 4))), // +5
        newDecl(ds, "t5", F,
                    newProof(ps, Proof::NOT_E, newProof(ps, i + 1), newProof(ps, i + 5))), // +6
        newDecl(ds, Decl::POP),
        // +0: p : SPROP
        // +1: (not (p or not p) -> p -> (p or not p))
        // +2: (not (p or not p) -> p -> false)
        // +3: (not (p or not p) -> not p)
        // +4: (not (p or not p) -> (p or not p))
        // +5: (not (p or not p) -> false)
        newDecl(ds, "t6", nullptr /* p or not p*/,
                    newProof(ps, Proof::RAA, newProof(ps, i + 5))), // +6
        newDecl(ds, Decl::POP),
        // +0: (forallpred p/0, not (p or not p) -> p -> (p or not p))
        // +1: (forallpred p/0, not (p or not p) -> p -> false)
        // +2: (forallpred p/0, not (p or not p) -> not p)
        // +3: (forallpred p/0, not (p or not p) -> (p or not p))
        // +4: (forallpred p/0, not (p or not p) -> false)
        // +5: (forallpred p/0, p or not p)
      });
    
    d->check(ctx, pool);

    Decl* d1 =
      newDecl(ds, block{
        newDecl(ds, "x", 0, SVAR), // +6
        newDecl(ds, "y", 0, SVAR), // +7
        newDecl(ds, "t7", nullptr /* x = y or not x = y */,
                    newProof(ps, Proof::FORALL2_E, newProof(ps, i + 5), newProof(ps, fv(eq, fv(i + 6), fv(i + 7))))), // +8
        newDecl(ds, Decl::POP),
        newDecl(ds, Decl::POP),
        // +6: (forall x y, x = y not x = y)
      });
    
    d1->check(ctx, pool);

    Decl* d2 =
      newDecl(ds, block{
        newDecl(ds, "q", 2, SPROP), // +7
        newDecl(ds, "x", 0, SVAR), // +8
        newDecl(ds, "y", 0, SVAR), // +9
        newDecl(ds, "t8", bin(fv(i + 7, fv(i + 8), fv(i + 9)), OR, un(NOT, fv(i + 7, fv(i + 8), fv(i + 9)))),
                    newProof(ps, Proof::FORALL2_E, newProof(ps, i + 5), newProof(ps, fv(i + 7, fv(i + 8), fv(i + 9))))), // +10
        newDecl(ds, Decl::POP),
        newDecl(ds, Decl::POP),
        newDecl(ds, Decl::POP),
        // +7: (forallpred q/2, forall x y, q x y or not q x y)
      });
    
    d2->check(ctx, pool);

    for (size_t i = 0; i < ctx.nextIndex(); i++) {
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
    unsigned int i = ctx.nextIndex();

    Decl* d =
      newDecl(ds, block{
        newDecl(ds, "x", 0, SVAR), // +0
        newDecl(ds, "y", 0, SVAR), // +1
        newDecl(ds, Decl::PDEF, "phi", "phi_def",
                    bin(fv(eq, fv(i + 0), fv(i + 1)), AND, fv(eq, fv(i + 1), fv(i + 0)))), // +2, +3
        newDecl(ds, Decl::POP),
        newDecl(ds, Decl::POP)
        // +0: phi: SVAR -> SVAR -> SPROP
        // +1: phi_def : (forall x y, phi x y <-> (x = y and y = x))
      });
    
    d->check(ctx, pool);

    Decl* d1 =
      newDecl(ds, block{
        newDecl(ds, "+", 2, SVAR), // +2
        newDecl(ds, "x", 0, SVAR), // +3
        newDecl(ds, "y", 0, SVAR), // +4
        newDecl(ds, "h1", fv(eq, fv(i + 3), fv(i + 4))), // +5
        newDecl(ds, Decl::FDEF, "f", "f_def",
                    fv(i + 2, fv(i + 3), fv(i + 4))), // +6, +7
        newDecl(ds, Decl::POP),
        newDecl(ds, Decl::POP),
        newDecl(ds, Decl::POP)
        // +2: +: SVAR -> SVAR -> SVAR
        // +3: f: SVAR -> SVAR -> SVAR
        // +4: f_def : (forall x y, x = y -> f x y = x + y)
      });

    d1->check(ctx, pool);

    for (size_t i = 0; i < ctx.nextIndex(); i++) {
      cout << ctx.nameOf(i) << ": ";
      if (holds_alternative<Type>(ctx[i])) cout << showType(get<Type>(ctx[i])) << endl;
      if (holds_alternative<const Expr*>(ctx[i])) cout << get<const Expr*>(ctx[i])->toString(ctx) << endl;
    }
  }

  return 0;
}
