#include <iostream>
#include <iomanip>
#include <string>
#include <initializer_list>
#include "core.hpp"
#include "elab/tableau.hpp"
#include "elab/procs.hpp"

using std::string;
using std::cin, std::cout, std::endl;
using namespace Core;
using enum Expr::Tag;
using enum Expr::SortTag;
using enum Expr::VarTag;
using enum FOLContext::Constant;


// TODO: read text & binary files

int main() {

  cout << sizeof(string) << endl;
  cout << sizeof(Expr) << endl;

  #define N(...) Expr::make(pool, __VA_ARGS__)

  #define fv(id)          N(VFree,  id)
  #define bv(id)          N(VBound, id)
  #define uv(id)          N(VMeta,  id)
  #define prop            N(SProp)
  #define type            N(SType)
  #define setvar          fv(SetVar)
  #define app(l, r)       N(l, r)
  #define lam(s, t, r)    N(Expr::LLam, s, t, r)
  #define pi(s, t, r)     N(Expr::PPi, s, t, r)

  #define tt              fv(True)
  #define ff              fv(False)
  #define un(var, a)      app(fv(var), a)
  #define bin(a, var, b)  app(app(fv(var), a), b)
  #define forall(s, a)    app(fv(Forall), lam(s, setvar, a))
  #define exists(s, a)    app(fv(Exists), lam(s, setvar, a))
  #define unique(s, a)    app(fv(Unique), lam(s, setvar, a))

  {
    FOLContext ctx;
    Allocator<Expr> pool;

    auto in = ctx.pushAssumption("in", pi("x", setvar, pi("y", setvar, prop)));

    // The axiom schema of separation...
    const auto x =
      lam("phi", pi("", setvar, pi("", setvar, prop)),
        forall("x", exists("y", forall("a", bin(bin(bv(0), in, bv(1)), Iff, bin(bin(bv(0), in, bv(2)), And, app(app(bv(3), bv(2)), bv(0))))))));

    cout << x->toString(ctx) << endl;
    cout << x->checkType(ctx, pool)->toString(ctx) << endl;

    auto subset = ctx.pushAssumption("subset", pi("P", pi("x", setvar, pi("a", setvar, prop)), pi("x", setvar, setvar)));
    auto issc = ctx.pushAssumption("is_subclass", pi("P", pi("x", setvar, prop), pi("Q", pi("x", setvar, prop), prop)));

    const auto y = lam("x", setvar, bin(lam("y", setvar, lam("z", setvar, tt)), subset, bv(0)));

    cout << y->toString(ctx) << endl;
    cout << y->checkType(ctx, pool)->toString(ctx) << endl;

    const auto z = bin(lam("x", setvar, ff), issc, lam("x", setvar, tt));

    cout << z->toString(ctx) << endl;
    cout << z->checkType(ctx, pool)->toString(ctx) << endl;

    cout << (*x == *y) << (*y == *z) << (*z == *x) << endl;
    cout << (*x == *x) << (*y == *y) << (*z == *z) << endl;

    const auto x1 = x->clone(pool);
    const auto xrep = Expr(x, lam("x", setvar, lam("y", setvar, bin(bv(1), Equals, bv(0))))).reduce(pool);

    cout << (*x == *x1) << endl;
    cout << xrep->toString(ctx) << endl;
    cout << FOLForm::fromExpr(xrep).toString(ctx) << endl;
    cout << xrep->checkType(ctx, pool)->toString(ctx) << endl;
    cout << endl;
  }

#if 0

  {
    FOLContext ctx;
    Allocator<Expr> pool;
    Allocator<Proof> ps;
    Allocator<Decl> ds;

    #define block std::initializer_list<Decl*>

    uint64_t eq = ctx.equals;
    uint64_t i = ctx.size();

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
        Decl::make(ds, "t5", FF,
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
    cout << endl;
  }

  {
    FOLContext ctx;
    Allocator<Expr> pool;
    Allocator<Proof> ps;
    Allocator<Decl> ds;

    uint64_t eq = ctx.equals;
    uint64_t i = ctx.size();

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

#endif

  {
    using namespace Elab;
    Allocator<Expr> pool;
    FOLContext ctx;
    Tableau tableau(ctx);

    uint64_t p = ctx.pushAssumption("p", prop);
    uint64_t q = ctx.pushAssumption("q", prop);
    uint64_t r = ctx.pushAssumption("r", prop);
    uint64_t s = ctx.pushAssumption("s", prop);

    auto e = bin(bin(fv(p), Iff, fv(q)), Iff, un(Not, bin(fv(r), Implies, fv(s))));
    cout << e->checkType(ctx, temp())->toString(ctx) << endl;
    cout << FOLForm::fromExpr(e).toString(ctx) << endl;
    auto snf = Procs::skolemize(un(Not, e), ctx, pool);
    cout << FOLForm::fromExpr(snf).toString(ctx) << endl;
    cout << Procs::showClauses(Procs::cnf(snf, pool), ctx) << endl;
    Elab::Procs::foreachValuation({ p, q, r, s }, [&e, &snf] (const vector<bool>& fvmap) {
      cout << Elab::Procs::propValue(e, fvmap);
      cout << !Elab::Procs::propValue(snf, fvmap);
    });
    cout << endl;
    cout << endl;

    cout << "(Not provable)" << endl;
    e = un(Not, bin(fv(p), Or, un(Not, fv(p))));
    cout << e->checkType(ctx, temp())->toString(ctx) << endl;
    cout << FOLForm::fromExpr(e).toString(ctx) << endl;
    snf = Procs::skolemize(un(Not, e), ctx, pool);
    cout << FOLForm::fromExpr(snf).toString(ctx) << endl;
    cout << Procs::showClauses(Procs::cnf(snf, pool), ctx) << endl;

    tableau.addSuccedent(e);
    cout << tableau.printState();
    cout << std::boolalpha << tableau.iterativeDeepening(11, 2) << endl;
    cout << tableau.printStats() << endl;
    tableau.clear();

    cout << "(Provable)" << endl;
    e = bin(fv(p), Or, un(Not, fv(p)));
    cout << e->checkType(ctx, temp())->toString(ctx) << endl;
    cout << FOLForm::fromExpr(e).toString(ctx) << endl;
    snf = Procs::skolemize(un(Not, e), ctx, pool);
    cout << FOLForm::fromExpr(snf).toString(ctx) << endl;
    cout << Procs::showClauses(Procs::cnf(snf, pool), ctx) << endl;

    tableau.addSuccedent(e);
    cout << tableau.printState();
    cout << std::boolalpha << tableau.iterativeDeepening(11, 2) << endl;
    cout << tableau.printStats() << endl;
    tableau.clear();

    // ¬(p ↔ ¬p)
    cout << "(Provable)" << endl;
    e = un(Not, bin(fv(p), Iff, un(Not, fv(p))));
    cout << e->checkType(ctx, temp())->toString(ctx) << endl;
    cout << FOLForm::fromExpr(e).toString(ctx) << endl;
    snf = Procs::skolemize(un(Not, e), ctx, pool);
    cout << FOLForm::fromExpr(snf).toString(ctx) << endl;
    cout << Procs::showClauses(Procs::cnf(snf, pool), ctx) << endl;

    tableau.addSuccedent(e);
    cout << tableau.printState();
    cout << std::boolalpha << tableau.iterativeDeepening(11, 2) << endl;
    cout << tableau.printStats() << endl;
    tableau.clear();
  }

  {
    using namespace Elab;
    Allocator<Expr> pool;
    FOLContext ctx;

    uint64_t lt  = ctx.pushAssumption("<", pi("x", setvar, pi("y", setvar, prop)));
    uint64_t mul = ctx.pushAssumption("*", pi("x", setvar, pi("y", setvar, setvar)));
    uint64_t x   = ctx.pushAssumption("x", setvar);
    uint64_t P   = ctx.pushAssumption("P", pi("x", setvar, prop));
    uint64_t Q   = ctx.pushAssumption("Q", pi("x", setvar, prop));

    auto e = exists("y", bin(bin(fv(x), lt, bv(0)), Implies, forall("u", exists("v", bin(bin(fv(x), mul, bv(1)), lt, bin(bv(2), mul, bv(0)))))));
    cout << e->checkType(ctx, temp())->toString(ctx) << endl;
    cout << FOLForm::fromExpr(e).toString(ctx) << endl;
    cout << FOLForm::fromExpr(Procs::skolemize(e, ctx, pool)).toString(ctx) << endl;

    e = forall("x", bin(app(fv(P), bv(0)), Implies, exists("y", exists("z", bin(app(fv(Q), bv(1)), Or, un(Not, exists("z", bin(app(fv(P), bv(0)), And, app(fv(Q), bv(0))))))))));
    cout << e->checkType(ctx, temp())->toString(ctx) << endl;
    cout << FOLForm::fromExpr(e).toString(ctx) << endl;
    cout << FOLForm::fromExpr(Procs::skolemize(e, ctx, pool)).toString(ctx) << endl;

    cout << endl;
  }

  {
    using namespace Elab::Procs;
    Allocator<Expr> pool;
    FOLContext ctx;

    uint64_t f = ctx.pushAssumption("f", pi("x", setvar, pi("y", setvar, setvar)));
    uint64_t g = ctx.pushAssumption("g", pi("x", setvar, pi("y", setvar, setvar)));
    uint64_t h = ctx.pushAssumption("h", pi("x", setvar, pi("y", setvar, setvar)));
    uint64_t a = ctx.pushAssumption("a", setvar);
    uint64_t b = ctx.pushAssumption("b", setvar);
    uint64_t x = ctx.pushAssumption("x", setvar);
    uint64_t y = ctx.pushAssumption("y", setvar);
    uint64_t z = ctx.pushAssumption("z", setvar);
    uint64_t u = ctx.pushAssumption("u", setvar);
    uint64_t v = ctx.pushAssumption("v", setvar);

    enum Meta: uint64_t { X, Y, Z, U, V };

    auto lhs = bin(app(app(fv(f), uv(X)), app(app(fv(g), uv(X)), uv(Y))), Equals, app(app(fv(h), uv(Z)), uv(Y)));
    auto rhs = bin(uv(Z), Equals, app(app(fv(h), app(app(fv(f), uv(U)), uv(V))), app(app(fv(f), fv(a)), fv(b))));
    auto lhs1 = app(app(fv(f), uv(X)), uv(Y));
    auto rhs1 = app(app(fv(f), uv(X)), app(app(fv(f), uv(X)), uv(Y)));

    cout << "First-order unification:" << endl;
    cout << lhs1->toString(ctx) << endl;
    cout << rhs1->toString(ctx) << endl;
    cout << unify({{ lhs1, rhs1 }}, pool).has_value() << endl;
    cout << endl;

    cout << lhs->toString(ctx) << endl;
    cout << rhs->toString(ctx) << endl;
    Subs subs = unify({{ lhs, rhs }}, pool).value();
    cout << showSubs(subs, ctx);
    cout << applySubs(lhs, subs, pool)->toString(ctx) << endl;
    cout << applySubs(rhs, subs, pool)->toString(ctx) << endl;
    cout << endl;

    // false false true
    cout << (*lhs == *rhs) << " " << equalAfterSubs(lhs, rhs, Subs()) << " " << equalAfterSubs(lhs, rhs, subs) << endl;
    cout << endl;

    auto lhs2 = bin(app(app(fv(f), fv(x)), app(app(fv(g), fv(x)), fv(y))), Equals, app(app(fv(h), fv(z)), fv(y)));
    auto rhs2 = bin(fv(z), Equals, app(app(fv(h), app(app(fv(f), fv(u)), fv(v))), app(app(fv(f), fv(a)), fv(b))));

    cout << "First-order anti-unification:" << endl;
    auto [tmpl, lsub, rsub] = antiunify(lhs2, rhs2, pool);
    cout << "Template: " << tmpl->toString(ctx) << endl;
    cout << "LHS substitution:" << endl << showSubs(lsub, ctx);
    cout << applySubs(lhs2, lsub, pool)->toString(ctx) << endl;
    cout << "RHS substitution:" << endl << showSubs(rsub, ctx);
    cout << applySubs(rhs2, rsub, pool)->toString(ctx) << endl;
    cout << endl;

    // Extra tests
    lhs = app(app(fv(f), uv(X)), uv(Y));
    rhs = app(app(fv(f), uv(Y)), uv(X));
    subs = unify({{ lhs, rhs }}, pool).value();
    cout << showSubs(subs, ctx);
    cout << applySubs(lhs, subs, pool)->toString(ctx) << endl;
    cout << applySubs(rhs, subs, pool)->toString(ctx) << endl;
    cout << endl;
  }

  {
    using namespace Elab;
    Allocator<Expr> pool;
    FOLContext ctx;
    Tableau tableau(ctx);

    uint64_t P = ctx.pushAssumption("P", pi("x", setvar, pi("y", setvar, prop)));
    uint64_t R = ctx.pushAssumption("R", pi("x", setvar, prop));
    uint64_t F = ctx.pushAssumption("F", pi("x", setvar, prop));
    uint64_t G = ctx.pushAssumption("G", pi("x", setvar, prop));
    uint64_t L = ctx.pushAssumption("Loves", pi("x", setvar, pi("y", setvar, prop)));
    uint64_t B = ctx.pushAssumption("BetterThan", pi("x", setvar, pi("y", setvar, pi("z", setvar, prop))));
    uint64_t Q = ctx.pushAssumption("QZR", setvar);

    auto lhs = exists("y", forall("x", app(app(fv(P), bv(0)), bv(1))));
    auto rhs = forall("x", exists("y", app(app(fv(P), bv(1)), bv(0))));

    cout << "(Provable)" << endl;
    tableau.addAntecedent(lhs);
    tableau.addSuccedent(rhs);
    cout << tableau.printState();
    cout << std::boolalpha << tableau.iterativeDeepening(11, 2) << endl;
    cout << tableau.printStats() << endl;
    tableau.clear();

    cout << "(Not provable)" << endl;
    tableau.addAntecedent(rhs);
    tableau.addSuccedent(lhs);
    cout << tableau.printState();
    cout << std::boolalpha << tableau.iterativeDeepening(11, 2) << endl;
    cout << tableau.printStats() << endl;
    tableau.clear();

    cout << "(Provable)" << endl;
    auto e = exists("x", forall("y", bin(app(fv(R), bv(1)), Implies, app(fv(R), bv(0)))));
    cout << e->checkType(ctx, temp())->toString(ctx) << endl;
    cout << FOLForm::fromExpr(e).toString(ctx) << endl;
    auto snf = Procs::skolemize(un(Not, e), ctx, pool);
    cout << FOLForm::fromExpr(snf).toString(ctx) << endl;
    cout << Procs::showClauses(Procs::cnf(snf, pool), ctx) << endl;

    tableau.addSuccedent(e);
    cout << tableau.printState();
    cout << std::boolalpha << tableau.iterativeDeepening(11, 2) << endl;
    cout << tableau.printStats() << endl;
    tableau.clear();

    cout << "(Provable)" << endl;
    e = bin(exists("y", exists("z", forall("x", bin(bin(app(fv(F), bv(0)), Implies, app(fv(G), bv(2))), And, bin(app(fv(G), bv(1)), Implies, app(fv(F), bv(0))))))),
      Implies, forall("x", exists("y", bin(app(fv(F), bv(1)), Iff, app(fv(G), bv(0))))));
    cout << e->checkType(ctx, temp())->toString(ctx) << endl;
    cout << FOLForm::fromExpr(e).toString(ctx) << endl;
    snf = Procs::skolemize(un(Not, e), ctx, pool);
    cout << FOLForm::fromExpr(snf).toString(ctx) << endl;
    cout << Procs::showClauses(Procs::cnf(snf, pool), ctx) << endl;

    tableau.addSuccedent(e);
    cout << tableau.printState();
    cout << std::boolalpha << tableau.iterativeDeepening(11, 2) << endl;
    cout << tableau.printStats() << endl;
    tableau.clear();

    cout << "(Provable)" << endl;
    auto exclusiveness = forall("x", forall("y", bin(app(app(fv(L), bv(1)), bv(0)), Implies, forall("z", bin(un(Not, bin(bv(0), Equals, bv(1))), Implies, un(Not, app(app(fv(L), bv(2)), bv(0))))))));
    auto preference = forall("x", forall("y", forall("z", bin(app(app(app(fv(B), bv(2)), bv(1)), bv(0)), Implies, bin(app(app(fv(L), bv(2)), bv(0)), Implies, app(app(fv(L), bv(2)), bv(1)))))));
    auto shadowing = exists("y", bin(un(Not, bin(bv(0), Equals, fv(Q))), And, forall("x", app(app(app(fv(B), bv(0)), bv(1)), fv(Q)))));
    auto goal = un(Not, exists("x", app(app(fv(L), bv(0)), fv(Q))));
    tableau.addAntecedent(exclusiveness);
    tableau.addAntecedent(preference);
    tableau.addAntecedent(shadowing);
    tableau.addSuccedent(goal);
    cout << tableau.printState();
    cout << std::boolalpha << tableau.iterativeDeepening(11, 2) << endl;
    cout << tableau.printStats() << endl;
    tableau.clear();
  }

  {
    using namespace Elab;
    Allocator<Expr> pool;
    FOLContext ctx;
    Tableau tableau(ctx);

    uint64_t P = ctx.pushAssumption("P", pi("x", setvar, prop));
    uint64_t Q = ctx.pushAssumption("Q", pi("x", setvar, prop));
    uint64_t R = ctx.pushAssumption("R", pi("x", setvar, prop));
    uint64_t f = ctx.pushAssumption("f", pi("x", setvar, setvar));
    uint64_t g = ctx.pushAssumption("g", pi("x", setvar, setvar));
    uint64_t a = ctx.pushAssumption("a", setvar);
    uint64_t b = ctx.pushAssumption("b", setvar);
    uint64_t rel = ctx.pushAssumption("R", pi("x", setvar, pi("y", setvar, prop)));
    uint64_t le = ctx.pushAssumption("<=", pi("x", setvar, pi("y", setvar, prop)));

    cout << "(Provable)" << endl;
    auto e1 = bin(app(fv(P), fv(a)), Or, app(fv(Q), fv(b)));
    auto e2 = forall("x", bin(app(fv(P), bv(0)), Implies, app(fv(R), bv(0))));
    auto e3 = forall("x", bin(app(fv(Q), bv(0)), Implies, app(fv(R), app(fv(f), bv(0)))));
    auto goal = exists("x", app(fv(R), bv(0)));
    tableau.addAntecedent(e1);
    tableau.addAntecedent(e2);
    tableau.addAntecedent(e3);
    tableau.addSuccedent(goal);
    cout << tableau.printState();
    cout << std::boolalpha << tableau.iterativeDeepening(11, 2) << endl;
    cout << tableau.printStats() << endl;
    tableau.clear();

    // This one is taking too long
    /*
    cout << "(Not provable)" << endl;
    e1 = forall("x", bin(app(fv(Q), bv(0)), Or, un(Not, app(fv(P), bv(0)))));
    e2 = app(fv(P), fv(a));
    goal = app(fv(Q), fv(b));
    tableau.addAntecedent(e1);
    tableau.addAntecedent(e2);
    tableau.addSuccedent(goal);
    cout << tableau.printState();
    cout << std::boolalpha << tableau.iterativeDeepening(11, 2) << endl;
    cout << tableau.printStats() << endl;
    tableau.clear();
    */

    cout << "(Provable!)" << endl;
    auto e = bin(
      forall("x", bin(
        bin(app(fv(P), fv(a)), And, bin(app(fv(P), bv(0)), Implies, exists("y", bin(app(fv(P), bv(0)), And, app(app(fv(rel), bv(1)), bv(0)))))),
        Implies,
        exists("z", exists("w", bin(bin(app(fv(P), bv(1)), And, app(app(fv(rel), bv(2)), bv(0))), And, app(app(fv(rel), bv(0)), bv(1)))))
      )),
      Iff,
      forall("x", bin(
        bin(
          bin(un(Not, app(fv(P), fv(a))), Or, app(fv(P), bv(0))),
          Or,
          exists("z", exists("w", bin(bin(app(fv(P), bv(1)), And, app(app(fv(rel), bv(2)), bv(0))), And, app(app(fv(rel), bv(0)), bv(1)))))),
        And,
        bin(
          bin(un(Not, app(fv(P), fv(a))), Or, un(Not, exists("y", bin(app(fv(P), bv(0)), And, app(app(fv(rel), bv(1)), bv(0)))))),
          Or,
          exists("z", exists("w", bin(bin(app(fv(P), bv(1)), And, app(app(fv(rel), bv(2)), bv(0))), And, app(app(fv(rel), bv(0)), bv(1)))))
        )
      ))
    );
    cout << e->checkType(ctx, temp())->toString(ctx) << endl;
    cout << FOLForm::fromExpr(e).toString(ctx) << endl;
    auto snf = Procs::skolemize(un(Not, e), ctx, pool);
    cout << FOLForm::fromExpr(snf).toString(ctx) << endl;
    cout << Procs::showClauses(Procs::cnf(snf, pool), ctx) << endl;

    tableau.addSuccedent(e);
    cout << tableau.printState();
    cout << std::boolalpha << tableau.iterativeDeepening(11, 2) << endl;
    cout << tableau.printStats() << endl;
    tableau.clear();

    cout << "(Provable!)" << endl;
    e1 = forall("x", app(app(fv(le), bv(0)), bv(0)));
    e2 = forall("x", forall("y", forall("z", bin(bin(app(app(fv(le), bv(2)), bv(1)), And, app(app(fv(le), bv(1)), bv(0))), Implies, app(app(fv(le), bv(2)), bv(0))))));
    e3 = forall("x", forall("y", bin(app(app(fv(le), app(fv(f), bv(1))), bv(0)), Iff, app(app(fv(le), bv(1)), app(fv(g), bv(0))))));
    goal = bin(
      forall("x", forall("y", bin(app(app(fv(le), bv(1)), bv(0)), Implies, app(app(fv(le), app(fv(f), bv(1))), app(fv(f), bv(0)))))),
      And,
      forall("x", forall("y", bin(app(app(fv(le), bv(1)), bv(0)), Implies, app(app(fv(le), app(fv(g), bv(1))), app(fv(g), bv(0))))))
    );
    tableau.addAntecedent(e1);
    tableau.addAntecedent(e2);
    tableau.addAntecedent(e3);
    tableau.addSuccedent(goal);
    /*
    const auto negated = bin(bin(bin(e1, And, e2), And, e3), And, un(Not, goal));
    tableau.addAntecedent(Procs::collectClauses(Procs::cnf(Procs::nnf(negated, pool), ctx, pool), pool));
    */

    cout << tableau.printState();
    // cout << std::boolalpha << tableau.iterativeDeepening(11, 2) << endl;
    cout << std::boolalpha << tableau.search(24, 11) << endl;
    cout << tableau.printStats() << endl;
    tableau.clear();
  }

  return 0;
}
