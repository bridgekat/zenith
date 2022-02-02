// ApiMu/FOL verifier v0.1 (C++ version)
// Licensed under Creative Commons CC0 (no copyright reserved, use at your will)

// This variant of FOL & ND is largely based on Dirk van Dalen's *Logic and Structure*...
// Additional features are described in `notes/design.md`.

// This is much more efficient compared to the Haskell version, but can be harder to read, and may contain (many) errors.
// Currently it does not support "private" and "undef".
// (I will need a parser and a pretty-printer to properly debug it...)

#include <iostream>
#include <initializer_list>
#include <vector>
#include <string>
#include <optional>
#include <variant>
#include <exception>

using std::initializer_list;
using std::vector;
using std::string;
using std::pair, std::make_pair;
using std::optional, std::make_optional, std::nullopt;
using std::variant, std::holds_alternative, std::get, std::get_if;
using std::cin, std::cout, std::endl;


// A simple region-based memory allocator: https://news.ycombinator.com/item?id=26433654
// This ensures that objects stay in the same place
template <typename T>
class Allocator {
private:
  size_t bSize, next;
  vector<T*> blocks;

public:
  Allocator(size_t blockSize = 1024): bSize(blockSize), next(0), blocks() {}
  Allocator(const Allocator&) = delete;
  Allocator& operator=(const Allocator&) = delete;
  ~Allocator() { for (auto p: blocks) delete[] p; }

  T* push_back(const T& obj) {
    if (next == 0) blocks.push_back(new T[bSize]);
    T* res = &blocks.back()[next];
    *res = obj;
    next++; if (next >= bSize) next = 0;
    return res;
  }

  size_t size() {
    if (next == 0) return bSize * blocks.size();
    return bSize * (blocks.size() - 1) + next;
  }
};


// Possible "types" of expressions (ι means Var, * means Prop):
//   Terms:      {{ 0, SVAR }}  (ι)
//   Functions:  {{ k, SVAR }}  (ι → ... → ι → ι)
//   Formulas:   {{ 0, SPROP }} (*)
//   Predicates: {{ k, SPROP }} (ι → ... → ι → *)
// Function/predicate schemas have "second-order parameters":
//   {{ k1, s1 }, { k2, s2 }} means ((ι → ... → ι → s1) → ι → ... → ι → s2), etc.
// (This is similar to Metamath definition checkers, according to Mario Carneiro!)
enum Sort: unsigned char { SVAR, SPROP };
typedef vector<pair<unsigned short, Sort>> Type;

const Type TTerm    = {{ 0, SVAR }};
const Type TFormula = {{ 0, SPROP }};

string showType(const Type& t) {
  string res = "";
  for (size_t i = 0; i < t.size(); i++) {
    string curr = "";
    for (int j = 0; j < t[i].first; j++) curr += "Var -> ";
    curr += (t[i].second == SVAR ? "Var" : "Prop");
    if (i + 1 < t.size()) curr = "(" + curr + ") -> ";
    res += curr;
  }
  return res;
}


class Context;
class Expr;
class Proof;
class Decl;

// Some exception classes...
struct CheckFailure: public std::logic_error { CheckFailure(const string& s): std::logic_error(s) {} };
struct InvalidExpr: public CheckFailure { InvalidExpr(const string& s, const Context& ctx, const Expr* e); };
struct InvalidProof: public CheckFailure { InvalidProof(const string& s, const Context& ctx, const Proof* e); };
struct InvalidDecl: public CheckFailure { InvalidDecl(const string& s, const Context& ctx, const Decl* e); };
struct Unreachable: public std::logic_error { Unreachable(): std::logic_error("\"Unreachable\" code was reached") {} };

// The context is stored as a stack (an std::vector whose last element denotes the topmost layer).
// Here, "assumed" and "defined" entries are interleaved, stored linearly in one array.
class Context {
public:
  // Context entry
  struct Entry {
    string name;
    variant<Type, const Expr*> info;
  };

  vector<Entry> a; // All entries
  vector<unsigned int> ind; // Indices of "assumed" entries
  const unsigned int eq;

  // Insert a built-in equality relation during initialization
  Context(): a(), ind(), eq(static_cast<unsigned int>(addDef("eq", {{ 2, SPROP }}))) {}

  // Add entries...
  size_t addDef         (const string& s, const Type& t) { a.push_back(Entry{ s, t }); return a.size() - 1; }
  size_t addTheorem     (const string& s, const Expr* e) { a.push_back(Entry{ s, e }); return a.size() - 1; }
  size_t pushVar        (const string& s, const Type& t) { a.push_back(Entry{ s, t }); ind.push_back(a.size() - 1); return a.size() - 1; }
  size_t pushAssumption (const string& s, const Expr* e) { a.push_back(Entry{ s, e }); ind.push_back(a.size() - 1); return a.size() - 1; }
  // Pops the last "assumed" entry, performs appropriate changes to all definitions and theorems in the top layer,
  // storing the new expressions in `pool`.
  // Returns false if there is no "assumed" entry left.
  bool pop(Allocator<Expr>& pool);

  // Look up by index.
  // Use `valid(i)` to perform bound checks before accessing, and throw appropriate exception if index is too large.
  size_t nextIndex() const { return a.size(); }
  bool valid(size_t index) const { return index < a.size(); }
  const variant<Type, const Expr*>& operator[](size_t index) const { return a.at(index).info; }
  const string& nameOf(size_t index) const { return a.at(index).name; }

  // Look up by literal name. (Slow, not commonly used)
  optional<unsigned int> lookup(const string& s) const {
    // Unsigned count down: https://nachtimwald.com/2019/06/02/unsigned-count-down/
    for (unsigned int i = static_cast<unsigned int>(a.size()); i --> 0;)
      if (a[i].name == s) return make_optional(i);
    return nullopt;
  }
};


const bool FREE = true;
const bool BOUND = false;

// Alphabet for a first-order language
enum Symbol: unsigned char {
  EMPTY = 0, // For default values only. EMPTY nodes are not well-formed terms or formulas.
  VAR, TRUE, FALSE, NOT, AND, OR, IMPLIES, IFF,
  FORALL, EXISTS, UNIQUE, FORALLFUNC, LAM
};

// Formula (schema) tree node, and related syntactic operations
// Pre (for all methods): there is no "cycle" throughout the tree
// Pre & invariant (for all methods): pointer is nonzero <=> pointer is valid (exception: root nodes have undefined *s pointer)
// Will just stick to this old-fashioned tagged union approach before C++ admits a better way to represent sum types
class Expr {
public:
  Symbol symbol;
  Expr* s = nullptr; // Next sibling (for children of VAR nodes only)
  union {
    // VAR (`id` stands for context index for free variables, de Brujin index for bound variables)
    struct { bool free; unsigned int id; Expr* c; } var;
    // TRUE, FALSE, NOT, AND, OR, IMPLIES, IFF (`l` is ignored for the first two; `r` is ignored for the first three)
    struct { Expr* l, * r; } conn;
    // FORALL, EXISTS, UNIQUE, FORALLFUNC, LAM (`arity` and `sort` must be 0 and SVAR for the first three and the last one)
    struct { unsigned short arity; Sort sort; Expr* r; } binder;
  };

  // The constructors below guarantee that all nonzero pointers (in the "active variant") are valid
  Expr(): symbol(EMPTY) {}
  Expr(Symbol sym): symbol(sym) {
    switch (sym) {
      case EMPTY: break;
      case VAR:
        var.c = nullptr; break;
      case TRUE: case FALSE: case NOT: case AND: case OR: case IMPLIES: case IFF:
        conn.l = conn.r = nullptr; break;
      case FORALL: case EXISTS: case UNIQUE: case FORALLFUNC: case LAM:
        binder.r = nullptr; break;
    }
  }
  // Assignment is shallow copy
  Expr(const Expr&) = default;
  Expr& operator=(const Expr&) = default;
  // Some convenient constructors (using no-copy attach)
  // TODO: check symbol
  Expr(Symbol sym, bool free, unsigned int id, const initializer_list<Expr*>& c): Expr(sym) {
    var.free = free; var.id = id; attachChildren(c);
  }
  Expr(Symbol sym, Expr* l): Expr(sym) { conn.l = l; }
  Expr(Symbol sym, Expr* l, Expr* r): Expr(sym) { conn.l = l; conn.r = r; }
  Expr(Symbol sym, unsigned short arity, Sort sort, Expr* r): Expr(sym) {
    binder.arity = arity; binder.sort = sort; binder.r = r;
  }

  // Deep copy
  // Pre: all nonzero pointers are valid
  // O(size)
  Expr* clone(Allocator<Expr>& pool) const {
    Expr* res = pool.push_back(*this);
    switch (symbol) {
      case EMPTY: break;
      case VAR: {
        Expr* last = nullptr;
        for (const Expr* p = var.c; p; p = p->s) {
          Expr* curr = p->clone(pool);
          (last? last->s : res->var.c) = curr;
          last = curr;
        }
        break;
      }
      case TRUE: case FALSE: case NOT: case AND: case OR: case IMPLIES: case IFF:
        if (conn.l) res->conn.l = (conn.l)->clone(pool);
        if (conn.r) res->conn.r = (conn.r)->clone(pool);
        break;
      case FORALL: case EXISTS: case UNIQUE: case FORALLFUNC: case LAM:
        if (binder.r) res->binder.r = (binder.r)->clone(pool);
        break;
    }
    return res;
  }

  // Attach children (no-copy)
  // Each node may only be attached to **one** parent node at a time!
  // Pre: symbol is VAR
  void attachChildren(const initializer_list<Expr*>& nodes) {
    if (symbol != VAR) return;
    Expr* last = nullptr;
    for (Expr* node: nodes) {
      (last? last->s : var.c) = node;
      last = node;
    }
  }

  // Syntactical equality
  // Pre: all nonzero pointers are valid
  // O(size)
  bool operator==(const Expr& rhs) const {
    if (symbol != rhs.symbol) return false;
    // symbol == rhs.symbol
    switch (symbol) {
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
      case FORALL: case EXISTS: case UNIQUE: case FORALLFUNC: case LAM:
        return binder.arity == rhs.binder.arity &&
              binder.sort  == rhs.binder.sort  &&
              *(binder.r)  == *(rhs.binder.r);
    }
    throw Unreachable();
  }
  bool operator!=(const Expr& rhs) const { return !(*this == rhs); }

  // Print
  // Pre: all nonzero pointers are valid
  // `stk` will be unchanged
  // O(size)
  string toString(const Context& ctx, vector<pair<Type, string>>& stk) const {
    switch (symbol) {
      case EMPTY: return "[?]";
      case VAR: {
        string res = var.free ?
          (ctx.valid(var.id)   ? ctx.nameOf(var.id)                  : "[?]") :
          (var.id < stk.size() ? stk[stk.size() - 1 - var.id].second : "[?]");
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
      case FORALL: case EXISTS: case UNIQUE: case FORALLFUNC: case LAM: {
        string ch, name(1, 'a' + stk.size()); // TODO: names for bound variables!
        switch (symbol) {
          case FORALL:     ch = "forall "; break;
          case EXISTS:     ch = "exists "; break;
          case UNIQUE:     ch = "unique "; break;
          case FORALLFUNC: ch = (binder.sort == SVAR ? "forallfunc " : "forallpred "); break;
          case LAM:        ch = "\\ "; break;
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
    throw Unreachable();
  }
  string toString(const Context& ctx) const {
    vector<pair<Type, string>> stk;
    return toString(ctx, stk);
  }

  // Check if the subtree is well-formed, and return its type
  // Throws exception on failure
  // Pre: all nonzero pointers are valid
  // `stk` will be unchanged
  // O(size)
  Type checkType(const Context& ctx, vector<Type>& stk) const {

    // Formation rules here
    switch (symbol) {
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
      case FORALLFUNC: {
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
    throw Unreachable();
  }
  Type checkType(const Context& ctx) const {
    vector<Type> stk;
    return checkType(ctx, stk);
  }

  // Modification (deep copying whole expression)
  // Pre: all nonzero pointers are valid
  // n = (number of binders on top of current node)
  template <typename F>
  Expr* updateVars(unsigned int n, Allocator<Expr>& pool, const F& f) const {
    // First shallow copy to pool
    Expr* res = pool.push_back(*this);
    switch (symbol) {
      case EMPTY: return res;
      case VAR: {
        // Modify subexpressions
        Expr* last = nullptr;
        for (const Expr* p = var.c; p; p = p->s) {
          Expr* q = p->updateVars(n, pool, f);
          (last? last->s : res->var.c) = q;
          last = q;
        }
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
      case FORALL: case EXISTS: case UNIQUE: case FORALLFUNC: case LAM:
        if (binder.r) res->binder.r = binder.r->updateVars(n + 1, pool, f);
        return res;
    }
    throw Unreachable();
  }

  // Make a free variable into an overflow variable (deep copying whole expression)
  Expr* makeBound(unsigned int id, Allocator<Expr>& pool) const {
    return updateVars(0, pool, [id] (unsigned int n, Expr* x) {
      if (x->var.free && x->var.id == id) { x->var.free = false; x->var.id = n; }
      return x;
    });
  }

  // Replace one overflow variable by an expression (deep copying whole expression)
  Expr* makeReplace(const Expr* t, Allocator<Expr>& pool) const {
    return updateVars(0, pool, [t, &pool] (unsigned int n, Expr* x) {
      if (!x->var.free && x->var.id == n) return t->clone(pool);
      return x;
    });
  }

  // Prepare to insert k binders around a subexpression with overflow variables (deep copying whole expression)
  Expr* makeGap(unsigned int k, Allocator<Expr>& pool) const {
    return updateVars(0, pool, [k] (unsigned int n, Expr* x) {
      if (!x->var.free && x->var.id >= n) x->var.id += k;
      return x;
    });
  }

  // Skip through lambda binders
  // Pre: expression must be well-formed
  pair<unsigned int, const Expr*> getBody() const {
    unsigned int res = 0;
    const Expr* p = this;
    while (p->symbol == LAM) p = p->binder.r, res++;
    return { res, p };
  }

  // Replace k overflow variables simultaneously, with t's possibly containing overflow variables...
  // (Deep copying whole expression)
  // Pre: ts.size() >= "maximum index overflow" (x->var.id - n + 1)
  Expr* makeReplaceK(vector<const Expr*> ts, Allocator<Expr>& pool) const {
    std::reverse(ts.begin(), ts.end()); // Leftmost arguments are used to substitute highest lambdas
    return updateVars(0, pool, [&ts, &pool] (unsigned int n, Expr* x) {
      if (!x->var.free && x->var.id >= n) return ts[x->var.id - n]->makeGap(n, pool);
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
    // Workaround for "structured bindings cannot be captured":
    // https://stackoverflow.com/questions/46114214/lambda-implicit-capture-fails-with-variable-declared-from-structured-binding
    return updateVars(0, pool, [k = k, body = body, &pool] (unsigned int n, Expr* x) {
      if (!x->var.free && x->var.id == n) {
        vector<const Expr*> args;
        for (const Expr* p = x->var.c; p; p = p->s) args.push_back(p);
        if (k != args.size()) throw Unreachable();
        return body->makeReplaceK(args, pool);
      }
      return x;
    });
  }

  // TODO: pretty print (infixl, infixr, precedence, etc.)
};

template<typename ...Ts>
inline Expr* newNode(Allocator<Expr>& pool, const Ts&... args) {
  return pool.push_back(Expr(args...));
}

// Context-changing rules (implies-intro, forall[func, pred]-intro) here
bool Context::pop(Allocator<Expr>& pool) {
  if (ind.empty()) return false;
  size_t index = ind.back(); ind.pop_back();
  auto entry = a[index];

  // Some helper functions and macros
  auto concat = [] (Type a, const Type& b) {
    for (auto x: b) a.push_back(x);
    return a;
  };

  #define node2(l_, sym_, r_)   newNode(pool, sym_, l_, r_)
  #define nodebinder(sym_, r_)  newNode(pool, sym_, 0, SVAR, r_) // This binds term variables only
  #define nodebinderks(sym_, k_, s_, r_) \
                                newNode(pool, sym_, k_, s_, r_)
  #define nodevar(f_, id_, ...) newNode(pool, VAR, f_, id_, initializer_list<Expr*>{__VA_ARGS__})
  #define isexpr(info)          holds_alternative<const Expr*>(info)
  #define istype(info)          holds_alternative<Type>(info)
  #define expr(info)            get<const Expr*>(info)
  #define type(info)            get<Type>(info)

  // Which kind of assumption?
  if (isexpr(entry.info)) {
    const Expr* hyp = expr(entry.info);

    for (size_t i = index; i + 1 < a.size(); i++) {
      // Copy a[i + 1] to a[i], with necessary modifications...
      if (isexpr(a[i + 1].info)) {
        // Implies-intro for theorems
        auto modify = [index, &pool] (unsigned int, Expr* x) {
          // If defined after the hypothesis...
          if (x->var.free && x->var.id > index) x->var.id--;
          return x;
        };
        a[i] = {
          a[i + 1].name,
          node2(hyp->clone(pool), IMPLIES, expr(a[i + 1].info)->updateVars(0, pool, modify))
        };
      } else if (istype(a[i + 1].info)) {
        // No change for definitions
        a[i] = a[i + 1];
      } else throw Unreachable();
    }
    a.pop_back();

  } else if (istype(entry.info)) {
    const Type& t = type(entry.info);
    // Assumed variable must be first- or second-order
    if (t.size() != 1) throw Unreachable();

    for (size_t i = index; i + 1 < a.size(); i++) {
      // Copy a[i + 1] to a[i], with necessary modifications...
      if (isexpr(a[i + 1].info)) {
        // Forall[func, pred]-intro for theorems
        auto modify = [index, &pool] (unsigned int n, Expr* x) {
          // If it is the assumed variable...
          if (x->var.free && x->var.id == index) {
            x->var.free = false; x->var.id = n;
          }
          // If defined after the assumed variable...
          else if (x->var.free && x->var.id > index) {
            x->var.id--;
            Expr* arg = nodevar(BOUND, n);
            arg->s = x->var.c; x->var.c = arg;
          }
          return x;
        };
        const Expr* ei = expr(a[i + 1].info);
        a[i] = {
          a[i + 1].name,
          (t == TTerm && ei->symbol != FORALLFUNC) ?
            nodebinder(FORALL, ei->updateVars(0, pool, modify)) :
            nodebinderks(FORALLFUNC, t[0].first, t[0].second, ei->updateVars(0, pool, modify))
        };
      } else if (istype(a[i + 1].info)) {
        // Add abstraction for definitions
        const Type& ti = type(a[i + 1].info);
        a[i] = {
          a[i + 1].name,
          (t == TTerm && ti.size() == 1) ?
            Type{{ ti[0].first + 1, ti[0].second }} :
            concat(t, ti)
        };
      } else throw Unreachable();
    }
    a.pop_back();

  } else throw Unreachable();

  #undef node2
  #undef nodebinder
  #undef nodebinderks
  #undef nodevar
  #undef isexpr
  #undef istype
  #undef expr
  #undef type
  return true;
}


class Decl;

// Derivation trees (aka. proof terms)
class Proof {
public:
  enum Rule: unsigned char {
    EMPTY = 0,
    EXPR, THM,
    AND_I, AND_L, AND_R, OR_L, OR_R, OR_E, IMPLIES_E, NOT_I, NOT_E, IFF_I, IFF_L, IFF_R, TRUE_I, FALSE_E, RAA,
    EQ_I, EQ_E, FORALL_E, EXISTS_I, EXISTS_E, UNIQUE_I, UNIQUE_L, UNIQUE_R, FORALLFUNC_E
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
  Proof(Expr* e): rule(EXPR) { expr.p = e; }
  Proof(unsigned int id): rule(THM) { thm.id = id; }
  Proof(Rule r, Proof* p0): rule(r) { subpfs.p[0] = p0; subpfs.p[1] = subpfs.p[2] = nullptr; }
  Proof(Rule r, Proof* p0, Proof* p1): rule(r) { subpfs.p[0] = p0; subpfs.p[1] = p1; subpfs.p[2] = nullptr; }
  Proof(Rule r, Proof* p0, Proof* p1, Proof* p2): rule(r) { subpfs.p[0] = p0; subpfs.p[1] = p1; subpfs.p[2] = p2; }

  // TODO: debug output

  Type checkExpr(const Context& ctx) const {
    switch (rule) {
      case EMPTY: throw InvalidProof("unexpected empty tag", ctx, this);
      case EXPR:
        if (!expr.p) throw InvalidProof("null pointer", ctx, this);
        return expr.p->checkType(ctx);
      default: throw InvalidProof("type mismatch, expected expression", ctx, this);
    }
  }

  // Checks proof (currently no side-effects on `ctx`)
  // Returned pointer is valid & points to a well-formed formula
  Expr* check(const Context& ctx, Allocator<Expr>& pool) const {

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
    //   sym_ must be a constant
    //   l_, r_ must be identifiers
    // Local variable x is used to prevent evaluating a_ multiple times
    // Throws exception on failure
    #define match0(a_, sym_) { \
      Expr* x = a_; \
      if (x->symbol != sym_) throw InvalidProof("incorrect main connective", ctx, this); \
    }
    #define match1(a_, sym_, l_) [[maybe_unused]] Expr* l_; { \
      Expr* x = a_; \
      if (x->symbol != sym_) throw InvalidProof("incorrect main connective", ctx, this); \
      if (!x->conn.l)        throw Unreachable(); \
      l_ = x->conn.l; \
    }
    #define match2(a_, l_, sym_, r_) [[maybe_unused]] Expr* l_, * r_; { \
      Expr* x = a_; \
      if (x->symbol != sym_)        throw InvalidProof("incorrect main connective", ctx, this); \
      if (!x->conn.l || !x->conn.r) throw Unreachable(); \
      l_ = x->conn.l, r_ = x->conn.r; \
    }
    #define matcheq(a_, l_, r_) Expr* l_, * r_; { \
      Expr* x = a_; \
      if (x->symbol != VAR || !x->var.free || x->var.id != ctx.eq) \
        throw InvalidProof("expected proof of equality", ctx, this); \
      l_ = x->var.c; r_ = l_->s; /* x is well-formed so we can expect exactly two child nodes here*/ \
    }
    #define matchbinder(a_, sym_, r_) [[maybe_unused]] Expr* r_; { \
      Expr* x = a_; \
      if (x->symbol != sym_) throw InvalidProof("incorrect binder", ctx, this); \
      if (!x->binder.r)      throw Unreachable(); \
      r_ = x->binder.r; \
    }
    #define asserteq(l_, r_) \
      if (*(l_) != *(r_)) throw InvalidProof("subexpressions should be equal", ctx, this)
    #define node0(sym_)           newNode(pool, sym_)
    #define node1(sym_, l_)       newNode(pool, sym_, l_)
    #define node2(l_, sym_, r_)   newNode(pool, sym_, l_, r_)
    #define nodebinder(sym_, r_)  newNode(pool, sym_, 0, SVAR, r_) // This binds term variables only
    #define nodevar(f_, id_, ...) newNode(pool, VAR, f_, id_, initializer_list<Expr*>{__VA_ARGS__})

    switch (rule) {
      case EMPTY: throw InvalidProof("unexpected empty tag", ctx, this);
      case EXPR:  throw InvalidProof("type mismatch, expected proof", ctx, this);
      case THM: {
        if (!ctx.valid(thm.id)) throw InvalidProof("referred theorem not in context", ctx, this);
        auto res = get_if<const Expr*>(&ctx[thm.id]);
        if (!res) throw InvalidProof("referred theorem not in context", ctx, this);
        return (*res)->clone(pool);
      }

      // Introduction & elimination rules here
      // (Manual pattern matching!)

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
      case IFF_I:     { match2(proved(0), p0, IMPLIES, q0); match2(proved(1), p1, IMPLIES, q1);
                        asserteq(p0, p1); asserteq(q0, q1); return node2(p0, IFF, q0); }
      case IFF_L: { match2(proved(0), p, IFF, q); asserteq(p, proved(1)); return q; }
      case IFF_R: { match2(proved(0), p, IFF, q); asserteq(q, proved(1)); return p; }
      case TRUE_I: return node0(TRUE);
      case FALSE_E: { match0(proved(0), FALSE); return wff(1)->clone(pool); }
      case RAA: { match2(proved(0), np, IMPLIES, f); match1(np, NOT, p); match0(f, FALSE); return p; }
      case EQ_I: {
        const Expr* t = wft(0);
        return nodevar(FREE, ctx.eq, t->clone(pool), t->clone(pool));
      }
      case EQ_E: {
        auto [p, type] = exprtype(0);
        if (!(p->symbol == LAM && type == Type{{ 1, SPROP }}))
          throw InvalidProof("type mismatch, expected unary predicate", ctx, this);
        Expr* px = p->binder.r, * pa = proved(2);
        matcheq(proved(1), a, b);
        asserteq(px->makeReplace(a, pool), pa);
        return px->makeReplace(b, pool);
      }
      case FORALL_E: {
        matchbinder(proved(0), FORALL, px);
        return px->makeReplace(wft(1), pool);
      }
      case EXISTS_I: {
        Expr* conc = wff(0)->clone(pool);
        matchbinder(conc, EXISTS, px);
        asserteq(px->makeReplace(wft(1), pool), proved(2));
        return conc;
      }
      case EXISTS_E: {
        matchbinder(proved(0), EXISTS, px0);
        matchbinder(proved(1), FORALL, px1q);
        match2(px1q, px1, IMPLIES, q);
        asserteq(px0, px1); asserteq(q, wff(2));
        return q;
      }
      case UNIQUE_I: {
        matchbinder(proved(0), EXISTS, px0);
        matchbinder(proved(1), FORALL, a); match2(a, px1, IMPLIES, b);
        matchbinder(b, FORALL, c);         match2(c, px2, IMPLIES, d);
        matcheq(d, l, r);
        if (!(l->symbol == VAR && !l->var.free && l->var.id == 1 &&
              r->symbol == VAR && !r->var.free && r->var.id == 0))
          throw InvalidProof("expected proof of uniqueness", ctx, this);
        asserteq(px0, px1); asserteq(px0, px2);
        return nodebinder(UNIQUE, px0);
      }
      case UNIQUE_L: {
        matchbinder(proved(0), UNIQUE, px);
        return nodebinder(EXISTS, px);
      }
      case UNIQUE_R: {
        matchbinder(proved(0), UNIQUE, px);
        return nodebinder(FORALL, node2(px, IMPLIES, nodebinder(FORALL, node2(px->clone(pool), IMPLIES,
                          nodevar(FREE, ctx.eq, nodevar(BOUND, 1), nodevar(BOUND, 0))))));
      }
      case FORALLFUNC_E: {
        // Check LHS
        Expr* p = proved(0);
        if (p->symbol != FORALLFUNC) throw InvalidProof("incorrect binder", ctx, this);
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
    throw Unreachable();
  }
};

template<typename ...Ts>
inline Proof* newProof(Allocator<Proof>& pool, const Ts&... args) {
  return pool.push_back(Proof(args...));
}


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
  Decl(const initializer_list<Decl*>& c): category(BLOCK) { attachChildren(c); }
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
  void attachChildren(const initializer_list<Decl*>& nodes) {
    if (category != BLOCK) return;
    Decl* last = nullptr;
    for (Decl* node: nodes) {
      (last? last->s : block.c) = node;
      last = node;
    }
  }

  // Checks declarations, side-effecting the context `ctx` (newly created expressions will be stored in `pool`)
  // Throws exception on failure
  void check(Context& ctx, Allocator<Expr>& pool) const {

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

    #define matchbinder(a_, sym_, r_) [[maybe_unused]] Expr* r_; { \
      Expr* x = a_; \
      if (x->symbol != sym_) throw InvalidDecl("incorrect binder", ctx, this); \
      if (!x->binder.r)      throw Unreachable(); \
      r_ = x->binder.r; \
    }
    #define node2(l_, sym_, r_)   newNode(pool, sym_, l_, r_)
    #define nodebinder(sym_, r_)  newNode(pool, sym_, 0, SVAR, r_) // This binds term variables only
    #define nodevar(f_, id_, ...) newNode(pool, VAR, f_, id_, initializer_list<Expr*>{__VA_ARGS__})

    switch (category) {
      case EMPTY: throw InvalidDecl("unexpected empty tag", ctx, this);
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

      case FDEF: {
        unsigned int id = ctx.addDef(name, TTerm);
        ctx.addTheorem(namedef, nodevar(FREE, ctx.eq, nodevar(FREE, id), wft(fdef.e)->clone(pool)));
        return;
      }
      case PDEF: {
        unsigned int id = ctx.addDef(name, TFormula);
        ctx.addTheorem(namedef, node2(nodevar(FREE, id), IFF, wff(pdef.e)->clone(pool)));
        return;
      }
      case DDEF: {
        matchbinder(proved(ddef.pf), UNIQUE, p);
        unsigned int id = ctx.addDef(name, TTerm);
        ctx.addTheorem(namedef, nodebinder(FORALL, node2(p, IFF, nodevar(FREE, ctx.eq, nodevar(BOUND, 0), nodevar(FREE, id)))));
        return;
      }
      case IDEF: {
        matchbinder(proved(idef.pf), EXISTS, p);
        unsigned int id = ctx.addDef(name, TTerm);
        ctx.addTheorem(namedef, p->makeReplace(nodevar(FREE, id), pool));
        return;
      }
      case UNDEF: {
        throw InvalidDecl("TODO", ctx, this);
      }
    }

    #undef matchbinder
    #undef node2
    #undef nodebinder
    #undef nodevar
    throw Unreachable();
  }
};

template<typename ...Ts>
inline Decl* newDecl(Allocator<Decl>& pool, const Ts&... args) {
  return pool.push_back(Decl(args...));
}

InvalidExpr::InvalidExpr(const string& s, const Context& ctx, const Expr* e):
  CheckFailure("Invalid expression, " + s + ": " + e->toString(ctx)) {}
InvalidProof::InvalidProof(const string& s, const Context&, const Proof*):
  CheckFailure("Invalid proof, " + s) {}
InvalidDecl::InvalidDecl(const string& s, const Context&, const Decl*):
  CheckFailure("Invalid expression, " + s) {}


// TODO: read text & binary files

int main() {
  cout << sizeof(string) << endl;
  cout << sizeof(Expr) << endl;
  cout << sizeof(Proof) << endl;
  cout << sizeof(Decl) << endl;

  #define N(...) newNode(pool, __VA_ARGS__)

  #define fv(id, ...) N(VAR, FREE,  id, initializer_list<Expr*>{__VA_ARGS__})
  #define bv(id, ...) N(VAR, BOUND, id, initializer_list<Expr*>{__VA_ARGS__})

  #define T                 N(TRUE)
  #define F                 N(FALSE)
  #define un(sym, a)        N(sym, a)
  #define bin(a, sym, b)    N(sym, a, b)
  #define forall(a)         N(FORALL, 0, SVAR, a)
  #define exists(a)         N(EXISTS, 0, SVAR, a)
  #define unique(a)         N(UNIQUE, 0, SVAR, a)
  #define forallpred(k, a)  N(FORALLFUNC, k, SPROP, a)
  #define forallfunc(k, a)  N(FORALLFUNC, k, SVAR, a)
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

    #define block initializer_list<Decl*>

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
                    newProof(ps, Proof::FORALLFUNC_E, newProof(ps, i + 5), newProof(ps, fv(eq, fv(i + 6), fv(i + 7))))), // +8
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
                    newProof(ps, Proof::FORALLFUNC_E, newProof(ps, i + 5), newProof(ps, fv(i + 7, fv(i + 8), fv(i + 9))))), // +10
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
