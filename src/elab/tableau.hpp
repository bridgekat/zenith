// Elab :: Tableau

#ifndef TABLEAU_HPP_
#define TABLEAU_HPP_

#include <vector>
#include <utility>
#include <unordered_set>
#include <core.hpp>
#include <iostream>


namespace Elab {

  using std::vector;
  using std::pair, std::make_pair;
  using std::unordered_set;
  using namespace Core;


  // (TEMP CODE)
  // Method of analytic tableaux (aka. sequent calculus) for classical logic
  // See: https://en.wikipedia.org/wiki/Method_of_analytic_tableaux
  // See: https://en.wikipedia.org/wiki/Sequent_calculus#The_system_LK
  class Tableau {
  public:

    // "Expression with hash" (a wrapper for `const Expr*` that overloads equality sign)
    struct ExprHash {
      const Expr* e;
      size_t hash;

      // `*e` should not be changed after this construction
      ExprHash(const Expr* e): e(e), hash(e->hash()) {}
      bool operator==(const ExprHash& r) const { return hash == r.hash && *e == *(r.e); }
      bool operator!=(const ExprHash& r) const { return hash != r.hash || *e != *(r.e); }

      struct GetHash {
        size_t operator()(const ExprHash& eh) const { return eh.hash; }
      };
    };

    vector<const Expr*> cedents[2];
    unordered_set<ExprHash, ExprHash::GetHash> hashset[2];

    Tableau(): cedents(), hashset() {}

    void addAntecedent(const Expr* e) {
      auto it = hashset[0].insert(ExprHash(e));
      if (it.second) cedents[0].push_back(e);
    }

    void addSuccedent(const Expr* e) {
      auto it = hashset[1].insert(ExprHash(e));
      if (it.second) cedents[1].push_back(e);
    }

    // TODO: initial check (the given proof state may already be closed)

    void clear() {
      hashset[0].clear();
      cedents[0].clear();
      hashset[1].clear();
      cedents[1].clear();
    }

    // Scope guard for "insert antecedents/succedents, check if closed, recurse, and remove them"
    template <unsigned int I, unsigned int J>
    class With {
    public:
      Tableau* const p;
      pair<unordered_set<ExprHash, ExprHash::GetHash>::iterator, bool> it;
      With(Tableau* p, const Expr* e, bool* closed): p(p), it() {
        ExprHash ehash = ExprHash(e);
        it = p->hashset[I].insert(ehash);
        if (it.second) {
          p->cedents[I].push_back(e);
          if (p->hashset[J].contains(ehash)) *closed = true;
        }
      }
      With(const With&) = delete;
      With& operator=(const With&) = delete;
      ~With() {
        if (it.second) {
          p->cedents[I].pop_back();
          p->hashset[I].erase(it.first);
        }
      }
    };
    using WithAnte = With<0, 1>;
    using WithSucc = With<1, 0>;

    // Pre: all elements of `ante`, `succ`, `anteSet` and `succSet` are valid, well-formed formulas
    // All states will be unmodified/restored
    bool dfs(size_t antei, size_t succi) {
      using enum Expr::Tag;
      auto ante = cedents[0], succ = cedents[1];

      if (antei < ante.size()) {
        const Expr* e = ante[antei];
        antei++;
        switch (e->tag) {
          case NOT: {
            bool closed = false;
            WithSucc n(this, e->conn.l, &closed);
            return closed || dfs(antei, succi);
          }
          case AND: {
            bool closed = false;
            WithAnte l(this, e->conn.l, &closed);
            WithAnte r(this, e->conn.r, &closed);
            return closed || dfs(antei, succi);
          }
          case OR: {
            {
              bool closed = false;
              WithAnte l(this, e->conn.l, &closed);
              if (!closed && !dfs(antei, succi)) return false;
            }
            {
              bool closed = false;
              WithSucc l(this, e->conn.l, &closed); // Optimization
              WithAnte r(this, e->conn.r, &closed);
              if (!closed && !dfs(antei, succi)) return false;
            }
            return true;
          }
          case IMPLIES: {
            {
              bool closed = false;
              WithSucc n(this, e->conn.l, &closed);
              if (!closed && !dfs(antei, succi)) return false;
            }
            {
              bool closed = false;
              WithAnte l(this, e->conn.l, &closed); // Optimization
              WithAnte r(this, e->conn.r, &closed);
              if (!closed && !dfs(antei, succi)) return false;
            }
            return true;
          }
          case IFF: {
            Expr mp(IMPLIES, e->conn.l, e->conn.r);
            Expr mpr(IMPLIES, e->conn.r, e->conn.l);
            bool closed = false;
            WithAnte l(this, &mp, &closed);
            WithAnte r(this, &mpr, &closed);
            return closed || dfs(antei, succi);
          }
          default:
            return dfs(antei, succi);
        }
      }

      if (succi < succ.size()) {
        const Expr* e = succ[succi];
        succi++;
        switch (e->tag) {
          case NOT: {
            bool closed = false;
            WithAnte n(this, e->conn.l, &closed);
            return closed || dfs(antei, succi);
          }
          case AND: {
            {
              bool closed = false;
              WithSucc l(this, e->conn.l, &closed);
              if (!closed && !dfs(antei, succi)) return false;
            }
            {
              bool closed = false;
              WithAnte l(this, e->conn.l, &closed); // Optimization
              WithSucc r(this, e->conn.r, &closed);
              if (!closed && !dfs(antei, succi)) return false;
            }
            return true;
          }
          case OR: {
            bool closed = false;
            WithSucc l(this, e->conn.l, &closed);
            WithSucc r(this, e->conn.r, &closed);
            return closed || dfs(antei, succi);
          }
          case IMPLIES: {
            bool closed = false;
            WithAnte l(this, e->conn.l, &closed);
            WithSucc r(this, e->conn.r, &closed);
            return closed || dfs(antei, succi);
          }
          case IFF: {
            Expr mp(IMPLIES, e->conn.l, e->conn.r);
            Expr mpr(IMPLIES, e->conn.r, e->conn.l);
            {
              bool closed = false;
              WithSucc l(this, &mp, &closed);
              if (!closed && !dfs(antei, succi)) return false;
            }
            {
              bool closed = false;
              WithAnte l(this, &mp, &closed); // Optimization
              WithSucc r(this, &mpr, &closed);
              if (!closed && !dfs(antei, succi)) return false;
            }
            return true;
          }
          default:
            return dfs(antei, succi);
        }
      }

      return false;
    }
  };

}

#endif // TABLEAU_HPP_
