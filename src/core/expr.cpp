#include "expr.hpp"
#include <type_traits>


namespace Core {

  using std::string;
  using std::vector;


  // Allow throwing in `noexcept` functions; we really intend to terminate with an error message
  #pragma GCC diagnostic push
  #pragma GCC diagnostic ignored "-Wterminate"

  Expr* Expr::clone(Allocator<Expr>& pool) const {
    switch (tag) {
      case Type: return make(pool, type.tag, type.l? type.l->clone(pool) : nullptr, type.r? type.r->clone(pool) : nullptr);
      case Var: return make(pool, var.tag, var.id);
      case App: return make(pool, app.l? app.l->clone(pool) : nullptr, app.r? app.r->clone(pool) : nullptr);
      case Lam: return make(pool, lam.s, lam.t? lam.t->clone(pool) : nullptr, lam.r? lam.r->clone(pool) : nullptr);
    }
    throw NotImplemented();
  }

  bool Expr::operator==(const Expr& rhs) const noexcept {
    if (this == &rhs) return true;
    if (tag != rhs.tag) return false;
    // tag == rhs.tag
    #define nullorsame(x) (!x && !rhs.x || x && rhs.x && *x == *rhs.x)
    switch (tag) {
      case Type: return type.tag == rhs.type.tag && nullorsame(type.l) && nullorsame(type.r);
      case Var: return var.tag == rhs.var.tag && var.id == rhs.var.id;
      case App: return nullorsame(app.l) && nullorsame(app.r);
      case Lam: return nullorsame(lam.t) && nullorsame(lam.r); // Ignore bound variable names
    }
    #undef nullorsame
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
      case Type:
        hash_combine(res, static_cast<std::underlying_type_t<TypeTag>>(type.tag));
        hash_combine(res, type.l? type.l->hash() : 0);
        hash_combine(res, type.r? type.r->hash() : 0);
        return res;
      case Var:
        hash_combine(res, static_cast<std::underlying_type_t<VarTag>>(var.tag));
        hash_combine(res, var.id);
        return res;
      case App:
        hash_combine(res, app.l? app.l->hash() : 0);
        hash_combine(res, app.r? app.r->hash() : 0);
        return res;
      case Lam:
        // Ignore bound variable names
        hash_combine(res, lam.t? lam.t->hash() : 0);
        hash_combine(res, lam.r? lam.r->hash() : 0);
        return res;
    }
    throw NotImplemented();
  }

  // Give unnamed bound variables a random name
  inline string newName(size_t i) {
    string res = "__";
    do {
      res.push_back('a' + i % 26);
      i /= 26;
    } while (i > 0);
    return res;
  }

  // Undefined variables and null pointers should be OK, as long as non-null pointers are valid.
  string Expr::toString(const Context& ctx, vector<string>& stk) const {
    switch (tag) {
      case Type: return
        type.tag == TFun ? "(" + (type.l? type.l->toString(ctx, stk) : "@Null") + " -> " + (type.r? type.r->toString(ctx, stk) : "@Null") + ")":
        type.tag == TVar ? "var" :
        type.tag == TProp ? "prop" : "@Null";
      case Var: return
        var.tag == VBound ? (var.id < stk.size() ? stk[stk.size() - 1 - var.id] : "@B" + std::to_string(var.id)) :
        var.tag == VFree  ? (ctx.valid(var.id)   ? ctx.nameOf(var.id)           : "@F" + std::to_string(var.id)) :
        var.tag == VMeta  ? "@M" + std::to_string(var.id) : "@Null";
      case App: return (app.l? app.l->toString(ctx, stk) : "@Null") + " " + (app.r? app.r->toString(ctx, stk) : "@Null");
      case Lam: {
        string name = lam.s.empty()? newName(stk.size()) : lam.s;
        string res = "(fun" + name + " : " + (lam.t? lam.t->toString(ctx, stk) : "@Null");
        stk.push_back(name); res += " => " + (lam.r? lam.r->toString(ctx, stk) : "@Null") + ")";
        stk.pop_back();
        return res;
      }
    }
    throw NotImplemented();
  }

  const Expr* Expr::checkType(const Context& ctx, Allocator<Expr>& pool, vector<const Expr*>& stk) const {
    switch (tag) {
      case Type: {
        switch (type.tag) {
          case TKind: throw InvalidExpr("\"kind\" does not have a type", ctx, this);
          case TFun:
            if (!type.l || !type.r) throw InvalidExpr("unexpected null pointer", ctx, this);
            if (*type.l->checkType(ctx, pool, stk) != Expr(TKind)) throw InvalidExpr("type expected", ctx, type.l);
            if (*type.r->checkType(ctx, pool, stk) != Expr(TKind)) throw InvalidExpr("type expected", ctx, type.r);
            return pool.emplaceBack(TKind);
          case TVar:  return pool.emplaceBack(TKind);
          case TProp: return pool.emplaceBack(TKind);
        }
      }
      case Var: {
        const Expr* t =
          var.tag == VBound ? (var.id < stk.size() ? stk[stk.size() - 1 - var.id] : nullptr) :
          var.tag == VFree  ? (ctx.valid(var.id)   ? ctx[var.id]                  : nullptr) :
          nullptr;
        if (!t)
          throw InvalidExpr(
            var.tag == VBound ? "de Bruijn index too large" :
            var.tag == VFree  ? "free variable not in context" :
            var.tag == VMeta  ? "unexpected metavariable" :
            "unknown variable tag: " + static_cast<std::underlying_type_t<VarTag>>(var.tag), ctx, this);
        return t->clone(pool);
      }
      case App: {
        if (!app.l || !app.r) throw InvalidExpr("unexpected null pointer", ctx, this);
        const Expr* tl = app.l->checkType(ctx, pool, stk);
        const Expr* tr = app.r->checkType(ctx, pool, stk);
        if (tl->tag != Type || tl->type.tag != TFun) throw InvalidExpr("function expected, term has type " + tl->toString(ctx), ctx, app.l);
        if (!tl->type.l || !tl->type.r) throw Unreachable(); // By postcondition of checkType(), returned type expression is well-formed
        if (*tl->type.l != *tr) throw InvalidExpr("argument type mismatch, expected " + tl->type.l->toString(ctx) + ", got " + tr->toString(ctx), ctx, app.r);
        return tl->type.r;
      }
      case Lam: {
        if (!lam.t || !lam.r) throw InvalidExpr("unexpected null pointer", ctx, this);
        if (*lam.t->checkType(ctx, pool, stk) != Expr(TKind)) throw InvalidExpr("type expected", ctx, lam.t);
        stk.push_back(lam.t);
        const Expr* tr = lam.r->checkType(ctx, pool, stk);
        stk.pop_back();
        return pool.emplaceBack(TFun, lam.t->clone(pool), tr);
      }
    }
    throw NotImplemented();
  }

  Expr* Expr::reduce(Allocator<Expr>& pool) const {
    switch (tag) {
      case Type: return make(pool, type.tag, type.l? type.l->reduce(pool) : nullptr, type.r? type.r->reduce(pool) : nullptr);
      case Var: return make(pool, var.tag, var.id);
      case App: {
        Expr* l = app.l? app.l->reduce(pool) : nullptr;
        Expr* r = app.r? app.r->reduce(pool) : nullptr;
        if (l && r && l->tag == Lam) return l->lam.r->makeReplace(r, pool)->reduce(pool);
        return make(pool, l, r);
      }
      case Lam: return make(pool, lam.s, lam.t? lam.t->reduce(pool) : nullptr, lam.r? lam.r->reduce(pool) : nullptr);
    }
    throw NotImplemented();
  }

  size_t Expr::size() const noexcept {
    switch (tag) {
      case Type: return 1 + (type.l? type.l->size() : 0) + (type.r? type.r->size() : 0);
      case Var: return 1;
      case App: return 1 + (app.l? app.l->size() : 0) + (app.r? app.r->size() : 0);
      case Lam: return 1 + (lam.t? lam.t->size() : 0) + (lam.r? lam.r->size() : 0);
    }
    throw NotImplemented();
  }

  bool Expr::occurs(VarTag vartag, uint64_t id) const noexcept {
    switch (tag) {
      case Type: return (type.l && type.l->occurs(vartag, id)) || (type.r && type.r->occurs(vartag, id));
      case Var: return var.tag == vartag && var.id == id;
      case App: return (app.l && app.l->occurs(vartag, id)) || (app.r && app.r->occurs(vartag, id));
      case Lam: return (lam.t && lam.t->occurs(vartag, id)) || (lam.r && lam.r->occurs(vartag, id));
    }
    throw NotImplemented();
  }

  size_t Expr::numUndetermined() const noexcept {
    switch (tag) {
      case Type: return std::max(type.l? type.l->numUndetermined() : 0, type.r? type.r->numUndetermined() : 0);
      case Var: return var.tag == VMeta? (var.id + 1) : 0;
      case App: return std::max(app.l? app.l->numUndetermined() : 0, app.r? app.r->numUndetermined() : 0);
      case Lam: return std::max(lam.t? lam.t->numUndetermined() : 0, lam.r? lam.r->numUndetermined() : 0);
    }
    throw NotImplemented();
  }

  #pragma GCC diagnostic pop

}
