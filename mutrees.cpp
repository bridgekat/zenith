// ApiMu/FOL verifier v0.1 (C++ version)
// Licensed under Creative Commons CC0 (no copyright reserved, use at your will)

// This variant of FOL & ND is largely based on Dirk van Dalen's *Logic and Structure*...
// Additional features are described in `notes/design.md`.

// This is more efficient compared to the Haskell version, but it can be harder to read,
// and may contain (many) errors.

#include <iostream>
#include <stdio.h>
#include <initializer_list>
#include <vector>
#include <set>
#include <map>
#include <algorithm>
#include <optional>
#include <variant>
#include <string>
#include <sstream>
#include <cassert>

using std::initializer_list;
using std::vector;
using std::set;
using std::map;
using std::pair, std::make_pair;
using std::tuple, std::get, std::make_tuple;
using std::optional, std::make_optional, std::nullopt;
using std::variant, std::holds_alternative, std::get_if;
using std::string;
using std::cin, std::cout, std::endl;


// A simple region-based memory allocator: https://news.ycombinator.com/item?id=26433654
// This ensures that objects stay in the same place
template <typename T>
class Allocator {
private:
  size_t bSize, next;
  vector<T*> blocks;

public:
  Allocator(size_t blockSize = 1024): bSize(blockSize), next(0) {}
  Allocator(const Allocator&) = delete;
  Allocator& operator=(const Allocator&) = delete;
  ~Allocator() { for (auto p: blocks) delete[] p; }

  T& push_back(const T& obj) {
    if (next == 0) blocks.push_back(new T[bSize]);
    T& res = blocks.back()[next];
    res = obj;
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
typedef vector<pair<unsigned short, Sort> > Type;

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

class Node;

// The context is stored as a stack (an std::vector whose last element denotes the topmost layer).
// Here, all hypotheses and definitions are stored "linearly" in one array.
class Context {
public:
  // Context entry
  struct Entry {
    string name;
    variant<Type, const Node*> info;
  };

  Allocator<Node> pool;
  vector<Entry> a;
  const unsigned int eq;

  // Insert a built-in equality relation during initialization
  Context(): eq(static_cast<unsigned int>(addDef("eq", {{ 2, SPROP }}))) {}

  // Add a definition to the top.
  size_t addDef(const string& s, const Type& t) { a.push_back(Entry{ s, t }); return a.size() - 1; }
  // Add a hypothesis to the top, copying the expression to pool.
//	size_t addHyp(const string& s, const Node* e) { a.push_back(Entry{ s, e->clone(pool) }); return a.size() - 1; }

  // Look up by index.
  bool valid(size_t index) const { return index < a.size(); }
  const variant<Type, const Node*>& operator[](size_t index) const { return a[index].info; }
  const string& nameOf(size_t index) const { return a[index].name; }

  // Look up by literal name. (Slow, not commonly used)
  optional<unsigned int> lookup(const string& s) const {
    // Unsigned count down: https://nachtimwald.com/2019/06/02/unsigned-count-down/
    for (unsigned int i = static_cast<unsigned int>(a.size()); i --> 0;)
      if (a[i].name == s) return make_optional(i);
    return nullopt;
  }

  unsigned int lookup1(const string& s) const {
    auto res = lookup(s);
    if (!res.has_value()) cout << "lookup1: unknown identifier " << s << endl;
    return res.value();
  }
};

// Formula (schema) tree node, and related syntactic operations
// Pre (for all methods): there is no "cycle" throughout the tree
// Pre & invariant (for all methods): pointer is nonzero <=> pointer is valid (exception: root nodes have undefined *s pointer)
class Node {
public:
  // Alphabet for a first-order language with equality
  enum Symbol: unsigned char {
    EMPTY = 0, // For default values only. EMPTY nodes are not well-formed terms or formulas.
    VAR, TRUE, FALSE, NOT, AND, OR, IMPLIES, IFF,
    FORALL, EXISTS, UNIQUE, FORALLFUNC, LAM
  } symbol;

  // Union-like classes: https://en.cppreference.com/w/cpp/language/union
  union {
    // VAR (`id` stands for context index for free variables, de Brujin index for bound variables)
    struct { bool free; unsigned int id; Node* c; } var;
    // TRUE, FALSE, NOT, AND, OR, IMPLIES, IFF (`l` is ignored for the first two; `r` is ignored for the first three)
    struct { Node* l, * r; } conn;
    // FORALL, EXISTS, UNIQUE, FORALLFUNC, LAM (`arity` and `sort` must be 0 and SVAR for the first three and the last one)
    struct { unsigned short arity; Sort sort; Node* r; } binder;
  };

  Node* s; // Next sibling (for children of PRED and FUNC nodes only)

  // Implicitly-defined default constructor does nothing: https://en.cppreference.com/w/cpp/language/default_constructor
  // The constructors below guarantee that all nonzero pointers (in the "active variant") are valid
  Node(): symbol(EMPTY), s(nullptr) {}
  Node(Symbol sym): symbol(sym), s(nullptr) {
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
  // Some convenient constructors (using unsafe attach)
  Node(Symbol sym, bool free, unsigned int id, const initializer_list<Node*>& c): Node(sym) {
    var.free = free; var.id = id; attachChildrenUnsafe(c);
  }
  Node(Symbol sym, Node* l):          Node(sym) { conn.l = l; }
  Node(Symbol sym, Node* l, Node* r): Node(sym) { conn.l = l; conn.r = r; }
  Node(Symbol sym, unsigned short arity, Sort sort, Node* r): Node(sym) {
    binder.arity = arity; binder.sort = sort; binder.r = r;
  }
  // Implicitly-defined copy constructor copies all non-static members: https://en.cppreference.com/w/cpp/language/copy_constructor
  // Node(const Node& rhs) = default;
  // Implicitly-defined move constructor moves all non-static members: https://en.cppreference.com/w/cpp/language/move_constructor
  // Node(Node&&) = default;
  // Implicitly-defined copy assignment operator copies all non-static members: https://en.cppreference.com/w/cpp/language/copy_assignment
  // Node& operator= (const Node&) = default;
  // Implicitly-defined move assignment operator moves all non-static members: https://en.cppreference.com/w/cpp/language/move_assignment
  // Node& operator= (Node&&) = default;
  // Implicitly-defined destructor does nothing: https://en.cppreference.com/w/cpp/language/destructor
  // ~Node() = default;

  // Deep copy
  // Pre: all nonzero pointers are valid
  // O(size)
  Node* clone(Allocator<Node>& pool) const {
    Node* res = &pool.push_back(*this);
    switch (symbol) {
    case EMPTY: break;
    case VAR: {
      Node* last = nullptr;
      for (const Node* p = var.c; p; p = p->s) {
        Node* curr = p->clone(pool);
        (last? last->s : res->var.c) = curr;
        last = curr;
      }
      }
      break;
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
  void attachChildrenUnsafe(const initializer_list<Node*>& nodes) {
    if (symbol != VAR) return;
    Node* last = nullptr;
    for (Node* node: nodes) {
      (last? last->s : var.c) = node;
      last = node;
    }
  }

  // Attach children (copying each node in the list)
  // Pre: symbol is VAR
  void attachChildren(const initializer_list<const Node*>& nodes, Allocator<Node>& pool) {
    if (symbol != VAR) return;
    Node* last = nullptr;
    for (const Node* cnode: nodes) {
      Node* node = cnode->clone(pool);
      (last? last->s : var.c) = node;
      last = node;
    }
  }

  // Syntactical equality
  // Pre: all nonzero pointers are valid
  // O(size)
  bool operator==(const Node& rhs) const {
    if (symbol != rhs.symbol) return false;
    // symbol == rhs.symbol
    switch (symbol) {
    case EMPTY: return true;
    case VAR: {
      if (var.free != rhs.var.free || var.id != rhs.var.id) return false;
      const Node* p = var.c, * prhs = rhs.var.c;
      for (; p && prhs; p = p->s, prhs = prhs->s) {
        if (!(*p == *prhs)) return false;
      }
      // Both pointers must be null at the same time
      if (p || prhs) return false;
      }
      return true;
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
    // Unreachable
    return false;
  }
  bool operator!=(const Node& rhs) const { return !(*this == rhs); }

  // Print
  // Pre: all nonzero pointers are valid
  // `stk` will be unchanged
  // O(size)
  string toString(const Context& ctx, vector<pair<Type, string> >& stk) const {
    switch (symbol) {
    case EMPTY: return "[?]";
    case VAR: {
      string res = var.free ?
        (ctx.valid(var.id)   ? ctx.nameOf(var.id)                  : "[?]") :
        (var.id < stk.size() ? stk[stk.size() - 1 - var.id].second : "[?]");
      for (const Node* p = var.c; p; p = p->s) {
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
    // Unreachable
    return "";
  }

  // Check if the subtree is well-formed, and return its type
  // Pre: all nonzero pointers are valid
  // `stk` will be unchanged
  // O(size)
  optional<Type> checkType(const Context& ctx, vector<Type>& stk) const {

    // Formation rules here
    switch (symbol) {
    case EMPTY:
      return nullopt;

    case VAR: {
      // Get type of the LHS
      const Type* t_ = var.free ?
        (ctx.valid(var.id)   ? get_if<Type>(&ctx[var.id])    : nullptr) :
        (var.id < stk.size() ? &stk[stk.size() - 1 - var.id] : nullptr);
      if (!t_ || t_->empty()) return nullopt;
      const Type& t = *t_;

      // Try applying arguments one by one
      size_t i = 0, j = 0;
      for (const Node* p = var.c; p; p = p->s) {
        auto tp_ = p->checkType(ctx, stk);
        if (!tp_.has_value()) return nullopt; // Subexpression does not typecheck
        const Type& tp = *tp_;

        if      (i + 1  < t.size() && tp.size() == 1 && tp[0] == t[i] ) i++; // Schema instantiation
        else if (i + 1 == t.size() && tp == TTerm    && j < t[i].first) j++; // Function application
        else return nullopt; // Types not match
      }

      if (i + 1 == t.size() && j == t[i].first) return Type{{ 0, t[i].second }}; // Fully applied
      else return nullopt; // Not fully applied
      }

    case TRUE: case FALSE:
      return TFormula;

    case NOT:
      if (conn.l && conn.l->checkType(ctx, stk) == TFormula) return TFormula;
      else return nullopt;

    case AND: case OR: case IMPLIES: case IFF:
      if (conn.l && conn.l->checkType(ctx, stk) == TFormula &&
          conn.r && conn.r->checkType(ctx, stk) == TFormula) return TFormula;
      else return nullopt;

    case FORALL: case EXISTS: case UNIQUE:
      if (binder.arity != 0 || binder.sort != SVAR) return nullopt;
      [[fallthrough]];
    case FORALLFUNC: {
      if (!binder.r) return nullopt;

      // Check recursively
      stk.push_back(Type{{ binder.arity, binder.sort }});
      auto t = binder.r->checkType(ctx, stk);
      stk.pop_back();

      if (t == TFormula) return TFormula;
      else return nullopt;
    }

    case LAM: {
      if (binder.arity != 0 || binder.sort != SVAR) return nullopt;
      if (!binder.r) return nullopt;

      // Check recursively
      stk.push_back(Type{{ binder.arity, binder.sort }});
      auto t = binder.r->checkType(ctx, stk);
      stk.pop_back();

      if (t.value().size() == 1) {
        auto [k, s] = t.value()[0];
        return Type{{ k + 1, s }};
      }
      else return nullopt;
    }
    }
    // Unreachable
    return nullopt;
  }

  // Modification (deep copying whole expression)
  // Pre: all nonzero pointers are valid
  // n = (number of binders on top of current node)
  template <typename F>
  Node* updateVars(unsigned int n, Allocator<Node>& pool, const F& f) const {
    // First shallow copy to pool
    Node* res = &pool.push_back(*this);
    switch (symbol) {
    case EMPTY: return res;
    case VAR: {
      // Modify subexpressions
      Node* last = nullptr;
      for (const Node* p = var.c; p; p = p->s) {
        Node* q = p->updateVars(n, pool, f);
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
    // Unreachable
    return res;
  }

  // Prepare to bind a free variable (deep copying whole expression)
  // Note that the resulting `this` is not well-formed until one additional layer of binder is added (there are "binding overflows by exactly one")
  Node* makeBound(unsigned int id, Allocator<Node>& pool) const {
    return updateVars(0, pool, [id] (unsigned int n, Node* x) {
      if (x->var.free && x->var.id == id) { x->var.free = false; x->var.id = n; }
      return x;
    });
  }

  // makeFree + replaceVar in one go (deep copying whole expression)
  // `this` can be a subexpression which is not well-formed by itself (there can be "binding overflows by exactly one")
  Node* makeReplace(const Node* t, Allocator<Node>& pool) const {
    return updateVars(0, pool, [t, &pool] (unsigned int n, Node* x) {
      if (!x->var.free && x->var.id == n) return t->clone(pool);
      return x;
    });
  }

  // Prepare to insert k binders around a subexpression (deep copying whole expression)
  // `this` can be a subexpression which is not well-formed by itself
  Node* makeGap(unsigned int k, Allocator<Node>& pool) const {
    return updateVars(0, pool, [k] (unsigned int n, Node* x) {
      if (!x->var.free && x->var.id >= n) x->var.id += k;
      return x;
    });
  }

  // Skip through lambda binders
  pair<unsigned int, const Node*> getBody() const {
    if (symbol == LAM) {
      auto [n, body] = binder.r->getBody();
      return { n + 1, body };
    }
    return { 0, this };
  }

  // Substitute in k overflow variables simultaneously, with t's possibly containing bound variables...
  // (Deep copying whole expression)
  // Pre: ts.size() >= "maximum index overflow" (x->var.id - n + 1)
  Node* makeReplaceK(vector<const Node*> ts, Allocator<Node>& pool) const {
    std::reverse(ts.begin(), ts.end()); // Leftmost arguments are used to substitute highest lambdas
    return updateVars(0, pool, [&ts, &pool] (unsigned int n, Node* x) {
      if (!x->var.free && x->var.id >= n) return ts[x->var.id - n]->makeGap(n, pool);
      return x;
    });
  }

  // Substitute in a lambda function (deep copying whole expression).
  // The 2nd argument is a lambda function/predicate with k lambda binders
  // In the 3rd argument, all applications of the "overflow-bound" function/predicate must have k arguments (will be checked)
  // To ensure that the resulting expression is well-formed, functions must be replaced by functions and
  // predicates must be replaced by predicates (i.e. types must match)
  Node* makeReplaceLam(const Node* lam, Allocator<Node>& pool) const {
    auto [k, body] = lam->getBody();
    // Workaround for "structured bindings cannot be captured":
    // https://stackoverflow.com/questions/46114214/lambda-implicit-capture-fails-with-variable-declared-from-structured-binding
    return updateVars(0, pool, [k = k, body = body, &pool] (unsigned int n, Node* x) {
      if (!x->var.free && x->var.id == n) {
        vector<const Node*> args;
        for (const Node* p = x->var.c; p; p = p->s) args.push_back(p);
        assert(k == args.size());
        return body->makeReplaceK(args, pool);
      }
      return x;
    });
  }

  // TODO: pretty print (infixl, infixr, precedence, etc.)
};

template<typename ...Ts>
Node* newNode(Allocator<Node>& pool, const Ts&... args) {
  return &pool.push_back(Node(args...));
}

/*
class Derivation {
public:
  enum Rule: unsigned int {
    EMPTY = 0,
    BLOCK,
    THM,
    AND_I, AND_L, AND_R,
    OR_L, OR_R, OR_E,
    IMPLIES_E,
    NOT_I, NOT_E,
    IFF_I, IFF_L, IFF_R,
    EQ_I, EQ_E,
    FORALL_E,
    EXISTS_I, EXISTS_E,
    UNIQUE_I, UNIQUE_E,
    FORALLFUNC_E,
    FORALLPRED_E,
    TRUE_I, FALSE_E, RAA
  } const rule;

  // Conclusion
  Node* a;

  // Auxiliary data (not going to put "non-POD" data types into a union...)
  string name;
  Node* tmpl;
  vector<unsigned int> loc;

  // Child derivations
  // DAGs are allowed (used in Fitch-style notation)
  vector<const Derivation*> c;
  // Assuming: pointer is present <=> pointer is valid

  // Implicitly-defined default constructor does nothing...
  Derivation(): rule(EMPTY), a(nullptr), tmpl(nullptr) {}
  Derivation(Rule r): rule(r), a(nullptr), tmpl(nullptr) {}

  // DAGs are allowed: each node may be attached to multiple parent nodes at a time
  void attachChildren(const initializer_list<const Derivation*>& nodes) {
    for (const Derivation* node: nodes) c.push_back(node);
  }

  // Check if a derivation is valid, given a set of axioms (cf. definitions in 1.4, 1.6, 2.8 and 2.9)
  // O((number of nodes) * (total size of hypotheses))
  // TODO: use hash tables to accelerate lookup?
  bool check(const Signature& sig, const map<string, const Node*>& theorems) const {
    auto res = check_(sig, theorems);
    return res.first && res.second.empty();
  }

private:

  // Returns: (current result, the set of uncancelled hypotheses)
  pair<bool, vector<const Node*> > check_(const Signature& sig, const map<string, const Node*>& theorems) const {
    pair<bool, vector<const Node*> > fail = { false, {} };
    vector<vector<const Node*> > hyps;
    // Check if initialized
    if (rule == EMPTY) return fail;
    // Check if conclusion is present and wff
    if (!a || !a->isForm(sig)) return fail;
    // Check if all premises are present, wff and valid; store all uncancelled hypotheses
    for (auto p: c) {
      if (!p) return fail;
      auto res = p->check_(sig, theorems);
      if (!res.first) return fail;
      hyps.push_back(res.second);
    }
    // Natural Deduction rules (major premises are listed first)
    switch (rule) {
    case THEOREM: {
      if (c.size() != 0) return fail;
      auto it = theorems.find(name);
      if (it == theorems.end() || *(it->second) != *a) return fail;
      return { true, {} };
    }
    case ASSUMPTION: {
      if (c.size() != 0) return fail;
      return { true, { a } };
    }
    case FUNCTION_S: {
      // #####
      return fail;
    }
    case CONJUNCTION_I: {
      if (c.size() != 2) return fail;
      const Node *l = c[0]->a, *r = c[1]->a;
      // Two premises l and r, conclusion in the form of (l ∧ r)
      if (a->symbol == Node::CONJUNCTION &&
        *(a->conn.l) == *l && *(a->conn.r) == *r)
        return { true, set_union(hyps[0], hyps[1]) };
      else return fail;
    }
    case CONJUNCTION_E: {
      if (c.size() != 1) return fail;
      const Node* p = c[0]->a;
      // One premise in the form of (l ∧ r), conclusion equals to l or r
      if (p->symbol == Node::CONJUNCTION &&
        (*a == *(p->conn.l) || *a == *(p->conn.r)))
        return { true, hyps[0] };
      else return fail;
    }
    case DISJUNCTION_I: {
      if (c.size() != 1) return fail;
      const Node* p = c[0]->a;
      // One premise p, conclusion in the form of (p ∨ r) or (l ∨ p)
      if (a->symbol == Node::DISJUNCTION &&
        (*(a->conn.l) == *p || *(a->conn.r) == *p))
        return { true, hyps[0] };
      else return fail;
    }
    case DISJUNCTION_E: {
      if (c.size() != 3) return fail;
      const Node *d = c[0]->a, *r0 = c[1]->a, *r1 = c[2]->a;
      // Three premises (p ∨ q), r, r, conclusion is r, cancelling hypotheses p, q in left, right
      if (d->symbol != Node::DISJUNCTION || *r0 != *r1) return fail;
      const Node *p = d->conn.l, *q = d->conn.r;
      if (*a == *r0)
        return { true, set_union(hyps[0],
                 set_union(ptr_set_minus_elem(hyps[1], p), ptr_set_minus_elem(hyps[2], q))) };
      else return fail;
    }
    case IMPLICATION_I: {
      if (c.size() != 1) return fail;
      const Node* p = c[0]->a;
      // One premise p, conclusion in the form of (q → p), cancelling hypothesis q
      if (a->symbol != Node::IMPLICATION || *(a->conn.r) != *p) return fail;
      const Node* q = a->conn.l;
      return { true, ptr_set_minus_elem(hyps[0], q) };
    }
    case IMPLICATION_E: {
      if (c.size() != 2) return fail;
      const Node *l = c[0]->a, *r = c[1]->a;
      // Two premises in the form of (p → q), p, conclusion is q
      if (l->symbol == Node::IMPLICATION &&
        (*r == *(l->conn.l) && *a == *(l->conn.r)))
        return { true, set_union(hyps[0], hyps[1]) };
      else return fail;
    }
    case NEGATION_I: {
      if (c.size() != 1) return fail;
      const Node* f = c[0]->a;
      // One premise ⊥, conclusion in the form of (¬p), cancelling hypothesis p
      if (a->symbol != Node::NEGATION || f->symbol != Node::ABSURDITY) return fail;
      const Node* p = a->conn.l;
      return { true, ptr_set_minus_elem(hyps[0], p) };
    }
    case NEGATION_E: {
      if (c.size() != 2) return fail;
      const Node *l = c[0]->a, *r = c[1]->a;
      // Two premises (¬p), p, conclusion is ⊥
      if (a->symbol != Node::ABSURDITY || l->symbol != Node::NEGATION) return fail;
      if (*r == *(l->conn.l))
        return { true, set_union(hyps[0], hyps[1]) };
      else return fail;
    }
    case EQUIVALENCE_I: {
      if (c.size() != 2) return fail;
      const Node *l = c[0]->a, *r = c[1]->a;
      // Two premises l, r, conclusion in the form of (l ↔ r), cancelling hypotheses r and l in left, right
      if (a->symbol != Node::EQUIVALENCE) return fail;
      if (*(a->conn.l) == *l && *(a->conn.r) == *r)
        return { true, set_union(ptr_set_minus_elem(hyps[0], r), ptr_set_minus_elem(hyps[1], l)) };
      else return fail;
    }
    case EFQ: {
      if (c.size() != 1) return fail;
      const Node* f = c[0]->a;
      // One premise in the form of ⊥
      if (f->symbol != Node::ABSURDITY) return fail;
      return { true, hyps[0] };
    }
    case RAA: {
      if (c.size() != 1) return fail;
      const Node* f = c[0]->a;
      // One premise in the form of ⊥, conclusion is p, cancelling hypotheses (¬p)
      if (f->symbol != Node::ABSURDITY) return fail;
      Node t(Node::NEGATION); t.conn.l = a;
      return { true, ptr_set_minus_elem(hyps[0], &t) };
    }
    case UNIVERSAL_I: {
      if (c.size() != 1) return fail;
      const Node* p = c[0]->a;
      // One premise p, conclusion in the form of (∀xi, p), with xi does not occur free in any hypothesis
      if (a->symbol != Node::UNIVERSAL || *(a->binder.r) != *p) return fail;
      unsigned int i = a->binder.l;
      for (const Node* hyp: hyps[0]) if (hyp->isFV(i)) return fail;
      return { true, hyps[0] };
    }
    case UNIVERSAL_E: {
      if (c.size() != 1) return fail;
      const Node* p = c[0]->a;
      // Check if t is present and well-formed
      const Node* t = tmpl;
      if (!t || !t->isForm(sig)) return fail;
      // One premise in the form of (∀xi, p), conclusion is p[t/xi]
      if (p->symbol != Node::UNIVERSAL) return fail;
      unsigned int i = p->binder.l;
      p = p->binder.r;
      // Check if substitution is "proper", or "free"
      if (!p->variableIsFreeFor(t, i)) return fail;
      // Do the substitution
      Allocator<Node> pool;
      Node* p_ = p->clone(pool);
      p_->replaceVariables({{ i, t }}, pool);
      // Check if results matched
      if (*p_ == *a)
        return { true, hyps[0] };
      else return fail;
    }
    case EXISTENTIAL_I: {
      if (c.size() != 1) return fail;
      const Node* p = c[0]->a;
      // Check if t is present and well-formed
      const Node* t = tmpl;
      if (!t || !t->isForm(sig)) return fail;
      // One premise q[t/xi], conclusion in the form of (∃xi, q)
      if (a->symbol != Node::EXISTENTIAL) return fail;
      unsigned int i = a->binder.l;
      const Node* q = a->binder.r;
      // Check if substitution is "proper", or "free"
      if (!q->variableIsFreeFor(t, i)) return fail;
      // Do the substitution
      Allocator<Node> pool;
      Node* q_ = q->clone(pool);
      q_->replaceVariables({{ i, t }}, pool);
      // Check if results matched
      if (*q_ == *p)
        return { true, hyps[0] };
      else return fail;
    }
    case EXISTENTIAL_E: {
      if (c.size() != 2) return fail;
      const Node *p = c[0]->a, *q = c[1]->a;
      // Two premises in the form of (∃xi, p) and q, with xi does not occur free in q or any hypothesis
      // from q (except p), conclusion is q, cancelling hypothesis p in right
      if (p->symbol != Node::EXISTENTIAL || *a != *q) return fail;
      unsigned int i = p->binder.l;
      p = p->binder.r;
      if (q->isFV(i)) return fail;
      for (const Node* hyp: hyps[1]) if (hyp->isFV(i) && *hyp != *p) return fail;
      return { true, set_union(hyps[0], ptr_set_minus_elem(hyps[1], p)) };
    }
    case EQUALITY_I: {
      if (c.size() != 0) return fail;
      // No premise, conclusion is in the form of (t = t)
      if (a->symbol != Node::PREDICATE || a->predicate.id != 0) return fail;
      const Node* l = a->predicate.c;
      const Node* r = l->s;
      if (*l == *r) return { true, {} };
      else return fail;
    }
    case EQUALITY_E: {
      if (c.size() < 1) return fail;
      int n = int(c.size()) - 1;
      const Node* q = c.back()->a;
      // Check if template is present and well-formed
      if (!tmpl || !tmpl->isForm(sig)) return fail;
      // Check if replacement locations are correct (duplicated or "invalid" entries are tolerated)
      if (loc.size() != n) return fail;
      // n major premises in the form of (li = ri), one minor premise
      // Minor premise and conclusion are equal to template substituted by li's and ri's respectively
      map<unsigned int, const Node*> qreps, areps;
      for (int i = 0; i < n; i++) {
        const Node* pi = c[i]->a;
        // Check if major premise i is in the correct form
        if (pi->symbol != Node::PREDICATE || pi->predicate.id != 0) return fail;
        const Node *li = pi->predicate.c, *ri = li->s;
        // Check if substitution is "proper", or "free"
        if (!tmpl->variableIsFreeFor(li, loc[i]) || !tmpl->variableIsFreeFor(ri, loc[i])) return fail;
        qreps[loc[i]] = li; areps[loc[i]] = ri;
      }
      // Do the substitution
      Allocator<Node> pool;
      Node *q_ = tmpl->clone(pool), *a_ = tmpl->clone(pool);
      q_->replaceVariables(qreps, pool); a_->replaceVariables(areps, pool);
      // Check if results matched
      if (*q == *q_ && *a == *a_) {
        vector<const Node*> allHyps;
        for (int i = 0; i < n; i++) allHyps = set_union(allHyps, hyps[i]);
        return { true, allHyps };
      } else return fail;
    }
    }
    return fail; // Unreachable
  }

public:

  // TODO: debug output
};

// A collection of axioms, definitions and theorems (derivations)
class Collection {
public:
  class Entry {
  public:
    enum ID {
      PUSH, POP,
      AXIOM_D, // Declaration of an axiom (schema)
      PREDICATE_D, FUNCTION_D, // Extension by definitions (using "shorthands")
      FUNCTION_DD, // Extension by definitions (using "definite descriptions")
//			FUNCTION_ID, // Extension by definitions (using "indefinite descriptions")
      PREDICATE_U, FUNCTION_U, // Undefining predicates and functions (removing all axioms/theorems that contain them)
      DERIVATION // A derivation to be checked
    } const id;

    // #####
  };

  // #####
};
*/

// TODO: read text & binary files

int main() {
  Allocator<Node> pool;

  #define N(...) newNode(pool, __VA_ARGS__)
  #define I initializer_list<Node*>

  #define FF(id, ...) N(Node::VAR, true,  id, I{__VA_ARGS__})
  #define BF(id, ...) N(Node::VAR, false, id, I{__VA_ARGS__})
  #define FV(id)      N(Node::VAR, true,  id, I{})
  #define BV(id)      N(Node::VAR, false, id, I{})

  #define TRUE             N(Node::TRUE)
  #define FALSE            N(Node::FALSE)
  #define NOT(a)           N(Node::NOT, a)
  #define AND(a, b)        N(Node::AND, a, b)
  #define OR(a, b)         N(Node::OR, a, b)
  #define IMPLIES(a, b)    N(Node::IMPLIES, a, b)
  #define IFF(a, b)        N(Node::IFF, a, b)
  #define FORALL(a)        N(Node::FORALL, 0, SVAR, a)
  #define EXISTS(a)        N(Node::EXISTS, 0, SVAR, a)
  #define UNIQUE(a)        N(Node::UNIQUE, 0, SVAR, a)
  #define FORALLPRED(k, a) N(Node::FORALLFUNC, k, SPROP, a)
  #define FORALLFUNC(k, a) N(Node::FORALLFUNC, k, SVAR, a)
  #define LAM(a)           N(Node::LAM, 0, SVAR, a)

  {
    Context ctx;
    vector<pair<Type, string> > stk;
    vector<Type> stk1;

    unsigned int EQ = ctx.eq;
    unsigned int IN = ctx.addDef("in", {{ 2, SPROP }});

    // The axiom schema of separation...
    Node* x = FORALLPRED(2, FORALL(EXISTS(FORALL(IFF(FF(IN, BV(0), BV(1)), AND(FF(IN, BV(0), BV(2)), BF(3, BV(2), BV(0))))))));

    cout << x->toString(ctx, stk) << endl;
    cout << showType(x->checkType(ctx, stk1).value()) << endl;

    unsigned int SUBSET = ctx.addDef("subset", {{ 2, SPROP }, { 1, SVAR }});
    unsigned int ISSC = ctx.addDef("is_subclass", {{ 1, SPROP }, { 1, SPROP }, { 0, SPROP }});

    Node* y = LAM(FF(SUBSET, LAM(LAM(TRUE)), BV(0)));

    cout << y->toString(ctx, stk) << endl;
    cout << showType(y->checkType(ctx, stk1).value()) << endl;

    Node* z = FF(ISSC, LAM(FALSE), LAM(TRUE));

    cout << z->toString(ctx, stk) << endl;
    cout << showType(z->checkType(ctx, stk1).value()) << endl;

    cout << (*x == *y) << (*y == *z) << (*z == *x) << endl;
    cout << (*x == *x) << (*y == *y) << (*z == *z) << endl;

    Node* x1 = x->clone(pool);
    Node* xrep = x->binder.r->makeReplaceLam(LAM(LAM(FF(EQ, BV(1), BV(0)))), pool);

    cout << (*x == *x1) << endl;
    cout << xrep->toString(ctx, stk) << endl;
    cout << showType(xrep->checkType(ctx, stk1).value()) << endl;
  }

  /* {
    Context ctx;
    vector<pair<Type, string> > stk;
    vector<Type> stk1;
  } */

  return 0;
}
