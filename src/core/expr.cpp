#include "expr.hpp"


namespace Core {

  Expr* Expr::clone(Allocator<Expr>& pool) const {
    Expr* res = pool.pushBack(*this);
    switch (tag) {
      case EMPTY: return res;
      case VAR: {
        Expr* last = nullptr;
        for (const Expr* p = var.c; p; p = p->s) {
          Expr* q = p->clone(pool);
          (last? last->s : res->var.c) = q;
          last = q;
        }
        (last? last->s : res->var.c) = nullptr;
        return res;
      }
      case TRUE: case FALSE: case NOT: case AND: case OR: case IMPLIES: case IFF:
        if (conn.l) res->conn.l = (conn.l)->clone(pool);
        if (conn.r) res->conn.r = (conn.r)->clone(pool);
        return res;
      case FORALL: case EXISTS: case UNIQUE: case FORALL2: case LAM:
        if (binder.r) res->binder.r = (binder.r)->clone(pool);
        return res;
    }
    throw NotImplemented();
  }

  void Expr::attachChildren(const std::initializer_list<Expr*>& nodes) noexcept {
    if (tag != VAR) return;
    Expr* last = nullptr;
    for (Expr* q: nodes) {
      (last? last->s : var.c) = q;
      last = q;
    }
    (last? last->s : var.c) = nullptr;
  }

  bool Expr::operator==(const Expr& rhs) const noexcept {
    if (tag != rhs.tag) return false;
    // tag == rhs.tag
    switch (tag) {
      case EMPTY: return true;
      case VAR: {
        if (var.free != rhs.var.free || var.id != rhs.var.id) return false;
        const Expr* p = var.c, * prhs = rhs.var.c;
        for (; p && prhs; p = p->s, prhs = prhs->s) {
          if (!(*p == *prhs)) return false;
        }
        // Both pointers must be null at the same time
        if (p || prhs) return false;
        return true;
      }
      case TRUE: case FALSE:
        return true;
      case NOT:
        return *(conn.l) == *(rhs.conn.l);
      case AND: case OR: case IMPLIES: case IFF:
        return *(conn.l) == *(rhs.conn.l) &&
               *(conn.r) == *(rhs.conn.r);
      case FORALL: case EXISTS: case UNIQUE: case FORALL2: case LAM:
        return binder.arity == rhs.binder.arity &&
               binder.sort  == rhs.binder.sort  &&
               *(binder.r)  == *(rhs.binder.r);
    }
    throw NotImplemented();
  }

  // Using: https://stackoverflow.com/questions/2590677/how-do-i-combine-hash-values-in-c0x
  template <class T>
  inline void hash_combine(size_t& seed, const T& v) noexcept {
    std::hash<T> hasher;
    seed ^= hasher(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
  }

  size_t Expr::hash() const noexcept {
    size_t res = static_cast<size_t>(tag);
    switch (tag) {
      case EMPTY: return res;
      case VAR: {
        hash_combine(res, var.free);
        hash_combine(res, var.id);
        for (const Expr* p = var.c; p; p = p->s) {
          hash_combine(res, p->hash());
        }
        return res;
      }
      case TRUE: case FALSE:
        return res;
      case NOT:
        hash_combine(res, conn.l->hash());
        return res;
      case AND: case OR: case IMPLIES: case IFF:
        hash_combine(res, conn.l->hash());
        hash_combine(res, conn.r->hash());
        return res;
      case FORALL: case EXISTS: case UNIQUE: case FORALL2: case LAM:
        hash_combine(res, binder.arity);
        hash_combine(res, binder.sort);
        hash_combine(res, binder.r->hash());
        return res;
    }
    throw NotImplemented();
  }

  // Give unnamed bound variables a name
  inline string newName(size_t i) {
    string res = "";
    do {
      res.push_back('a' + i % 26);
      i /= 26;
    } while (i > 0);
    return res;
  }

  // Undefined variables and null pointers should be OK, as long as non-null pointers are valid.
  string Expr::toString(const Context& ctx, vector<pair<Type, string>>& stk) const {
    switch (tag) {
      case EMPTY: return "[?]";
      case VAR: {
        string res = var.free ?
          (ctx.valid(var.id)   ? ctx.nameOf(var.id)                  : "[" + std::to_string(var.id) + "]") :
          (var.id < stk.size() ? stk[stk.size() - 1 - var.id].second : "{" + std::to_string(var.id) + "}");
        for (const Expr* p = var.c; p; p = p->s) {
          res += " " + p->toString(ctx, stk);
        }
        return var.c ? "(" + res + ")" : res;
      }
      case TRUE:    return "true";
      case FALSE:   return "false";
      case NOT:     return "not " + (conn.l ? conn.l->toString(ctx, stk) : "[?]");
      case AND:     return "(" + (conn.l ? conn.l->toString(ctx, stk) : "[?]") + " and "
                               + (conn.r ? conn.r->toString(ctx, stk) : "[?]") + ")";
      case OR:      return "(" + (conn.l ? conn.l->toString(ctx, stk) : "[?]") + " or "
                               + (conn.r ? conn.r->toString(ctx, stk) : "[?]") + ")";
      case IMPLIES: return "(" + (conn.l ? conn.l->toString(ctx, stk) : "[?]") + " implies "
                               + (conn.r ? conn.r->toString(ctx, stk) : "[?]") + ")";
      case IFF:     return "(" + (conn.l ? conn.l->toString(ctx, stk) : "[?]") + " iff "
                               + (conn.r ? conn.r->toString(ctx, stk) : "[?]") + ")";
      case FORALL: case EXISTS: case UNIQUE: case FORALL2: case LAM: {
        string ch, name = bv.empty() ? newName(stk.size()) : bv;
        switch (tag) {
          case FORALL:  ch = "forall "; break;
          case EXISTS:  ch = "exists "; break;
          case UNIQUE:  ch = "unique "; break;
          case FORALL2: ch = (binder.sort == SVAR ? "forallfunc " : "forallpred "); break;
          case LAM:     ch = "\\ "; break;
          default: break;
        }
        string res = "(" + ch + name;
        // If not an individual variable...
        if (!(binder.arity == 0 && binder.sort == SVAR)) {
          res += "/" + std::to_string(binder.arity);
          res += (binder.sort == SVAR ? "#" : "$");
        }
        // Print recursively
        stk.emplace_back(Type{{ binder.arity, binder.sort }}, name);
        res += ", " + binder.r->toString(ctx, stk) + ")";
        stk.pop_back();
        return res;
      }
    }
    throw NotImplemented();
  }

  Type Expr::checkType(const Context& ctx, vector<Type>& stk) const {

    // Formation rules here
    switch (tag) {
      case EMPTY:
        throw InvalidExpr("unexpected empty tag", ctx, this);

      case VAR: {
        // Get type of the LHS
        const Type* t_ = var.free ?
          (ctx.valid(var.id)   ? get_if<Type>(&ctx[var.id])    : nullptr) :
          (var.id < stk.size() ? &stk[stk.size() - 1 - var.id] : nullptr);
        if (!t_ || t_->empty())
          throw InvalidExpr(var.free? "free variable not in context" :
                                      "de Brujin index too large", ctx, this);
        const Type& t = *t_;

        // Try applying arguments one by one
        size_t i = 0, j = 0;
        for (const Expr* p = var.c; p; p = p->s) {
          const Type& tp = p->checkType(ctx, stk);
          if      (i + 1  < t.size() && tp.size() == 1 && tp[0] == t[i] ) i++; // Schema instantiation
          else if (i + 1 == t.size() && tp == TTerm    && j < t[i].first) j++; // Function application
          else throw InvalidExpr("argument type mismatch", ctx, this);
        }

        if (i + 1 == t.size() && j == t[i].first) return Type{{ 0, t[i].second }}; // Fully applied
        else throw InvalidExpr("function or predicate not fully applied", ctx, this);
      }

      case TRUE: case FALSE:
        return TFormula;

      case NOT:
        if (conn.l && conn.l->checkType(ctx, stk) == TFormula) return TFormula;
        else throw InvalidExpr("connective should connect propositions", ctx, this);

      case AND: case OR: case IMPLIES: case IFF:
        if (conn.l && conn.l->checkType(ctx, stk) == TFormula &&
            conn.r && conn.r->checkType(ctx, stk) == TFormula) return TFormula;
        else throw InvalidExpr("connective should connect propositions", ctx, this);

      case FORALL: case EXISTS: case UNIQUE:
        if (binder.arity != 0 || binder.sort != SVAR)
          throw InvalidExpr("binder should bind a term variable", ctx, this);
        [[fallthrough]];
      case FORALL2: {
        if (!binder.r)
          throw InvalidExpr("null pointer", ctx, this);

        // Check recursively
        stk.push_back(Type{{ binder.arity, binder.sort }});
        auto t = binder.r->checkType(ctx, stk);
        stk.pop_back();

        if (t == TFormula) return TFormula;
        else throw InvalidExpr("binder body should be a proposition", ctx, this);
      }

      case LAM: {
        if (binder.arity != 0 || binder.sort != SVAR)
          throw InvalidExpr("binder should bind a term variable", ctx, this);
        if (!binder.r)
          throw InvalidExpr("null pointer", ctx, this);

        // Check recursively
        stk.push_back(Type{{ binder.arity, binder.sort }});
        auto t = binder.r->checkType(ctx, stk);
        stk.pop_back();

        if (t.size() == 1) {
          auto [k, s] = t[0];
          return Type{{ k + 1, s }};
        }
        else throw InvalidExpr("function body has invalid type", ctx, this);
      }
    }

    throw NotImplemented();
  }

  bool Expr::occurs(unsigned int id) const noexcept {
    switch (tag) {
      case EMPTY:
        return false;
      case VAR:
        if (var.free && var.id == id) return true;
        for (const Expr* p = var.c; p; p = p->s) {
          if (p->occurs(id)) return true;
        }
        return false;
      case TRUE: case FALSE:
        return false;
      case NOT:
        return conn.l && conn.l->occurs(id);
      case AND: case OR: case IMPLIES: case IFF:
        return (conn.l && conn.l->occurs(id)) || (conn.r && conn.r->occurs(id));
      case FORALL: case EXISTS: case UNIQUE: case FORALL2: case LAM: 
        return binder.r && binder.r->occurs(id);
    }
    throw NotImplemented();
  }

}
