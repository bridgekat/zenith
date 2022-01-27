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

	// Insert a built-in equality relation during initialization
	Context() { unsigned int equality = static_cast<unsigned int>(addDef("eq", {{ 2, SPROP }})); }

	// Add a definition to the top.
	size_t addDef(const string& s, const Type& t) { a.emplace_back(s, t); return a.size() - 1; }
	// Add a hypothesis to the top, copying the expression to pool.
	size_t addHyp(const string& s, const Node* e) { a.emplace_back(s, e->treeClone(pool)); return a.size() - 1; }

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

// The C++ version makes use of a single global context.
Context context;

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
	} const symbol;

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
		case VAR:
			var.c = nullptr; break;
		case TRUE: case FALSE: case NOT: case AND: case OR: case IMPLIES: case IFF:
			conn.l = conn.r = nullptr; break;
		case FORALL: case EXISTS: case UNIQUE: case FORALLFUNC: case LAM:
			binder.r = nullptr; break;
		}
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

	// Count the number of child nodes
	// Pre: symbol is VAR; all nonzero pointers are valid
	unsigned int arity() const {
		if (symbol != VAR) return 0;
		unsigned int res = 0;
		for (const Node* p = var.c; p; p = p->s) res++;
		return res;
	}

	// Attach children (no-copy)
	// Each node may only be attached to **one** parent node at a time!
	// Pre: symbol is VAR
	void attachChildrenUnsafe(const std::initializer_list<Node*>& nodes) {
		if (symbol != VAR) return;
		Node* last = nullptr;
		for (Node* node: nodes) {
			(last? last->s : var.c) = node;
			last = node;
		}
	}

	// Deep copy
	// Pre: all nonzero pointers are valid
	// O(size)
	Node* treeClone(Allocator<Node>& pool) const {
		Node* res = &pool.push_back(*this);
		switch (symbol) {
		case EMPTY: break;
		case VAR: {
			Node* last = nullptr;
			for (const Node* p = var.c; p; p = p->s) {
				Node* curr = p->treeClone(pool);
				(last? last->s : res->var.c) = curr;
				last = curr;
			}
			}
			break;
		case TRUE: case FALSE: case NOT: case AND: case OR: case IMPLIES: case IFF:
			if (conn.l) res->conn.l = (conn.l)->treeClone(pool);
			if (conn.r) res->conn.r = (conn.r)->treeClone(pool);
			break;
		case FORALL: case EXISTS: case UNIQUE: case FORALLFUNC: case LAM:
			if (binder.r) res->binder.r = (binder.r)->treeClone(pool);
			break;
		}
		return res;
	}

	// Attach children (copying each node in the list)
	// Pre: symbol is VAR
	void attachChildren(const std::initializer_list<const Node*>& nodes, Allocator<Node>& pool) {
		if (symbol != VAR) return;
		Node* last = nullptr;
		for (const Node* cnode: nodes) {
			Node* node = cnode->treeClone(pool);
			(last? last->s : var.c) = node;
			last = node;
		}
	}

	// Pre: symbol is NOT, FORALL, EXISTS, UNIQUE, FORALLFUNC or LAM
	void attach(const Node* c, Allocator<Node>& pool) {
		switch (symbol) {
		case NOT:
			conn.l = c->treeClone(pool); break;
		case FORALL: case EXISTS: case UNIQUE: case FORALLFUNC: case LAM:
			binder.r = c->treeClone(pool); break;
		}
	}

	// Pre: symbol is AND, OR, IMPLIES or IFF
	void attachL(const Node* c, Allocator<Node>& pool) {
		switch (symbol) {
		case AND: case OR: case IMPLIES: case IFF:
			conn.l = c->treeClone(pool); break;
		}
	}

	// Pre: symbol is AND, OR, IMPLIES or IFF
	void attachR(const Node* c, Allocator<Node>& pool) {
		switch (symbol) {
		case AND: case OR: case IMPLIES: case IFF:
			conn.r = c->treeClone(pool); break;
		}
	}

	// Syntactical equality
	// Pre: all nonzero pointers are valid
	// O(size)
	bool operator==(const Node& rhs) const {
		if (symbol != rhs.symbol) return false;
		// symbol == rhs.symbol
		switch (symbol) {
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
				case LAM:        ch = "lambda "; break;
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

			if (i + 1 == t.size() && j == t[i].first) return TTerm; // Fully applied
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
			stk.emplace_back(binder.arity, binder.sort);
			auto t = binder.r->checkType(ctx, stk);
			stk.pop_back();

			if (t == TFormula) return TFormula;
			else return nullopt;
		}
		
		case LAM: {
			if (binder.arity != 0 || binder.sort != SVAR) return nullopt;
			if (!binder.r) return nullopt;

			// Check recursively
			stk.emplace_back(binder.arity, binder.sort);
			auto t = binder.r->checkType(ctx, stk);
			stk.pop_back();

			if (t.value().size() == 1) {
				auto [k, s] = t.value()[0];
				return Type{{ k + 1, s }};
			}
			else return nullopt;
		}
		}
		return nullopt;
	}

	// In-place modification
	// n = (number of binders on top of current node)
	template <typename F>
	Node* updateVars(unsigned int n, const F& f) {
		switch (symbol) {
		
		}
	}

	// TODO: pretty print (infixl, infixr, precedence, etc.)
};

Node* newNode(Node::Symbol sym, Allocator<Node>& pool) {
	return &pool.push_back(Node(sym));
}

/*

class Derivation {
public:
	enum Rule: unsigned int {
		EMPTY = 0,
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
	void attachChildren(const std::initializer_list<const Derivation*>& nodes) {
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
		/*
		* **Differences from the original van Dalen's version:**
		* The EQUIVALENCE_E rule simultaneously substitutes equivalent formulas across the whole premise, just like
		  EQUALITY_E (Justify by either semantic equivalence or induction on "depth".). This allows me to do
		  "α-conversion" (renaming bound variables) or "unfolding of definition" anywhere in a formula in one step.
		* Distinction is made between ASSUMPTION and THEOREM in order to handle metavariable specialization from within
		  a derivation.
		* The metavariable specialization rule: if a metavariable has arity K, replacing it by some ψ (or t) involves:
		  1. Changing bound variables in ψ to avoid naming clashes in Step 3.
		  2. Assigning new indices "unused across the whole derivation" to free variables with indices > K in ψ.
		  3. Substituting the free variables with indices 1..K in ψ for the child terms (the terms "in parentheses").
		* It can be proven if all metavariables inside a derivation are simultaneously specialized "consistently" (i.e.
		  the new indices given in Step 2 are the same), the derivation remains syntactically valid.
		* So Γ ⊢ φ by derivation D gives Γ_sub(D, ψ) ⊢ Γ_sub(D, ψ).
		* We may further "relax" the constraints in Step 2, by choosing indices "unused in all uncancelled hypotheses
		  and the conclusion", since the variables mentioned in the derivation which do not present in hypotheses or
		  conclusion can be renamed freely.
		* (It is easier to see that the rule is indeed semantically valid: we are just "restricting" arbitrary
		  predicates / functions to a specific subset of predicates / functions!)
		* Now note that the use of axiom schemata or previously-derived theorem schemata do not contribute to
		  "uncancelled hypotheses" - their derivation rely on no hypothesis, and in principle we may chain these
		  derivations together and do metavariable specialization on "the whole thing". (By definition, axiom schemata
		  can be specialized freely. Here we do not explicitly specialize them, just to make checking faster.)
		* We may "relax" the constraints even further, by allowing overlap between those "extra free variables" in
		  Step 2 and the "already-present free variables" in the original schema. Semantically it just imposes the same
		  "variable equality" restrictions on all the hypotheses and the conclusion, under which the entailment
		  relation should remain valid. Moreover, by applying →I, ∀I, ∀E, →E on the derivation of the "non-overlapped"
		  version, we could get a derivation for the "overlapped" version.
		
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
		case PREDICATE_S: {
			// #####
			return fail;
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
		case EQUIVALENCE_E: {
			if (c.size() < 1) return fail;
			int n = int(c.size()) - 1;
			const Node* q = c.back()->a;
			// Check if template is present and well-formed
			if (!tmpl || !tmpl->isForm(sig)) return fail;
			// Check if replacement locations are correct (duplicated or "invalid" entries are tolerated)
			if (loc.size() != n) return fail;
			// n major premises in the form of (li ↔ ri), one minor premise
			// Minor premise and conclusion are equal to template substituted by li's and ri's respectively
			map<unsigned int, const Node*> qreps, areps;
			for (int i = 0; i < n; i++) {
				const Node* pi = c[i]->a;
				// Check if major premise i is in the correct form
				if (pi->symbol != Node::EQUIVALENCE) return fail;
				const Node *li = pi->conn.l, *ri = pi->conn.r;
				// Check if substitution is "proper", or "free"
				if (!tmpl->propositionIsFreeFor(li, loc[i]) || !tmpl->propositionIsFreeFor(ri, loc[i])) return fail;
				qreps[loc[i]] = li; areps[loc[i]] = ri;
			}
			// Do the substitution
			Allocator<Node> pool;
			Node *q_ = tmpl->treeClone(pool), *a_ = tmpl->treeClone(pool);
			q_->replacePropositions(qreps, pool); a_->replacePropositions(areps, pool);
			// Check if results matched
			if (*q == *q_ && *a == *a_) {
				vector<const Node*> allHyps;
				for (int i = 0; i < n; i++) allHyps = set_union(allHyps, hyps[i]);
				return { true, allHyps };
			} else return fail;
		}
		case EQUIVALENCE_SYMM: {
			if (c.size() != 1) return fail;
			const Node* p = c[0]->a;
			// One premise in the form of (l ↔ r), conclusion is (r ↔ l)
			if (p->symbol != Node::EQUIVALENCE || a->symbol != Node::EQUIVALENCE) return fail;
			if (*(p->conn.l) == *(a->conn.r) && *(p->conn.r) == *(a->conn.l))
				return { true, hyps[0] };
			else return fail;
		}
		case EQUIVALENCE_TRANS: {
			if (c.size() != 2) return fail;
			const Node *l = c[0]->a, *r = c[1]->a;
			// Two premises in the form of (p ↔ q), (q ↔ s), conclusion is (p ↔ s)
			if (l->symbol != Node::EQUIVALENCE || r->symbol != Node::EQUIVALENCE ||
				a->symbol != Node::EQUIVALENCE) return fail;
			const Node *p = l->conn.l, *q0 = l->conn.r;
			const Node *q1 = r->conn.l, *s = r->conn.r;
			if (*q0 == *q1 && *(a->conn.l) == *p && *(a->conn.r) == *s)
				return { true, set_union(hyps[0], hyps[1]) };
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
			Node* p_ = p->treeClone(pool);
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
			Node* q_ = q->treeClone(pool);
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
			Node *q_ = tmpl->treeClone(pool), *a_ = tmpl->treeClone(pool);
			q_->replaceVariables(qreps, pool); a_->replaceVariables(areps, pool);
			// Check if results matched
			if (*q == *q_ && *a == *a_) {
				vector<const Node*> allHyps;
				for (int i = 0; i < n; i++) allHyps = set_union(allHyps, hyps[i]);
				return { true, allHyps };
			} else return fail;
		}
		case EQUALITY_SYMM: {
			if (c.size() != 1) return fail;
			const Node* p = c[0]->a;
			// One premise in the form of (s = t), conclusion is (t = s)
			if (p->symbol != Node::PREDICATE || p->predicate.id != 0 ||
				a->symbol != Node::PREDICATE || a->predicate.id != 0) return fail;
			const Node *s0 = p->predicate.c, *t0 = a->predicate.c;
			const Node *t1 = s0->s, *s1 = t0->s;
			if (*s0 == *s1 && *t0 == *t1)
				return { true, hyps[0] };
			else return fail;
		}
		case EQUALITY_TRANS: {
			if (c.size() != 2) return fail;
			const Node *l = c[0]->a, *r = c[1]->a;
			// Two premises in the form of (s = t), (t = u), conclusion is (s = u)
			if (l->symbol != Node::PREDICATE || l->predicate.id != 0 ||
				r->symbol != Node::PREDICATE || r->predicate.id != 0 ||
				a->symbol != Node::PREDICATE || a->predicate.id != 0) return fail;
			const Node *s0 = l->predicate.c, *t0 = r->predicate.c, *s1 = a->predicate.c;
			const Node *t1 = s0->s, *u0 = t0->s, *u1 = s1->s;
			if (*s0 == *s1 && *t0 == *t1 && *u0 == *u1)
				return { true, set_union(hyps[0], hyps[1]) };
			else return fail;
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

// TODO: read text & binary files

int main() {
	
	{ // Experiment 1
		Signature sig;
		const unsigned int ZERO = sig.addConstant("0");
		const unsigned int ADD = sig.addFunction("+", 2);
		const unsigned int MUL = sig.addFunction("*", 2);
		const unsigned int SUCC = sig.addFunction("S", 1);
		const unsigned int EQUAL = 0;
		const unsigned int LESS = sig.addPredicate("<", 2);
		const unsigned int LEQUAL = sig.addPredicate("≤", 2);

		Node p(Node::UNIVERSAL), q(Node::UNIVERSAL);
		p.binder.l = 1; q.binder.l = 2;
		Node a(Node::EQUIVALENCE), b(Node::PREDICATE), c(Node::DISJUNCTION), d(Node::PREDICATE), e(Node::PREDICATE);
		b.predicate.id = LEQUAL; d.predicate.id = LESS; e.predicate.id = EQUAL;
		Node x0(Node::VARIABLE), y0(Node::VARIABLE), x1(Node::VARIABLE), y1(Node::VARIABLE);
		Node x2(Node::VARIABLE), y2(Node::VARIABLE), x3(Node::VARIABLE), y3(Node::VARIABLE);
		x0.variable.id = x1.variable.id = x2.variable.id = x3.variable.id = 1;
		y0.variable.id = y1.variable.id = y2.variable.id = y3.variable.id = 2;

		cout << a.isTerm(sig) << a.isForm(sig) << e.isTerm(sig) << e.isForm(sig) << endl; // 0000
		a.conn.l = &b; a.conn.r = &c;
		cout << a.isForm(sig) << b.isForm(sig) << b.isTerm(sig) << endl; // 000
		b.attachChildrenUnsafe({ &x1, &y1 });
		cout << a.isForm(sig) << b.isForm(sig) << b.isTerm(sig) << endl; // 010
		c.conn.l = &d; c.conn.r = &e;
		cout << a.isForm(sig) << c.isForm(sig) << endl; // 00
		d.attachChildrenUnsafe({ &x2, &y2 });
		cout << a.isForm(sig) << c.isForm(sig) << endl; // 00
		e.attachChildrenUnsafe({ &x3, &y3 });
		cout << a.isForm(sig) << c.isForm(sig) << endl; // 11

		cout << b.toString(sig) << endl; // ≤(x1, x2)
		cout << a.toString(sig) << endl; // (≤(x1, x2) ↔ (<(x1, x2) ∨ =(x1, x2)))

		p.binder.r = &q; q.binder.r = &a;
		cout << p.toString(sig) << endl; // (∀x1, (∀x2, (≤(x1, x2) ↔ (<(x1, x2) ∨ =(x1, x2)))))

		cout << a.FV().size() << a.BV().size() << endl; // 20
		cout << q.FV().size() << q.BV().size() << endl; // 11
		cout << p.FV().size() << p.BV().size() << endl; // 02
		cout << a.isFV(1) << a.isFV(3) << p.isFV(1) << p.isFV(2) << endl; // 1000
	}

	{ // Experiment 2
		Signature sig;
		const unsigned int ZERO = sig.addConstant("0");
		const unsigned int ADD = sig.addFunction("+", 2);
		const unsigned int MUL = sig.addFunction("*", 2);
		const unsigned int SUCC = sig.addFunction("S", 1);
		const unsigned int EQUAL = 0;
		const unsigned int LESS = sig.addPredicate("<", 2);
		const unsigned int LEQUAL = sig.addPredicate("≤", 2);

		Allocator<Node> all;

		auto p = newNode(Node::UNIVERSAL, all); p->binder.l = 1;
		auto q = newNode(Node::UNIVERSAL, all); q->binder.l = 2;

		auto a = newNode(Node::EQUIVALENCE, all);
		auto b = newNode(Node::PREDICATE, all); b->predicate.id = LEQUAL;
		auto c = newNode(Node::DISJUNCTION, all);
		auto d = newNode(Node::PREDICATE, all); d->predicate.id = LESS;
		auto e = newNode(Node::PREDICATE, all); e->predicate.id = EQUAL;
		
		auto x = newNode(Node::VARIABLE, all); x->variable.id = 1;
		auto y = newNode(Node::VARIABLE, all); y->variable.id = 2;

		cout << all.size() << endl; // 9
		d->attachChildren({ x, y }, all);
		cout << all.size() << endl; // 11
		e->attachChildren({ x, y }, all);
		cout << all.size() << endl; // 13
		c->attachL(d, all); c->attachR(e, all);
		cout << all.size() << endl; // 19
		b->attachChildren({ x, y }, all);
		cout << all.size() << endl; // 21
		a->attachL(b, all); a->attachR(c, all);
		cout << all.size() << endl; // 31
		cout << a->isForm(sig) << c->isForm(sig) << endl; // 11

		cout << b->toString(sig) << endl; // ≤(x1, x2)
		cout << a->toString(sig) << endl; // (≤(x1, x2) ↔ (<(x1, x2) ∨ =(x1, x2)))

		q->attach(a, all); p->attach(q, all);
		cout << p->toString(sig) << endl; // (∀x1, (∀x2, (≤(x1, x2) ↔ (<(x1, x2) ∨ =(x1, x2)))))

		cout << a->FV().size() << a->BV().size() << endl; // 20
		cout << q->FV().size() << q->BV().size() << endl; // 11
		cout << p->FV().size() << p->BV().size() << endl; // 02
		cout << a->isFV(1) << a->isFV(3) << p->isFV(1) << p->isFV(2) << endl; // 1000

		auto zero = newNode(Node::CONSTANT, all); zero->constant.id = ZERO;
		auto one = newNode(Node::FUNCTION, all); one->function.id = SUCC; one->attachChildren({ zero }, all);
		auto two = newNode(Node::FUNCTION, all); two->function.id = SUCC; two->attachChildren({ one }, all);
		auto one_one = newNode(Node::FUNCTION, all); one_one->function.id = ADD; one_one->attachChildren({ one, one }, all);

		cout << a->toString(sig) << endl; // (≤(x1, x2) ↔ (<(x1, x2) ∨ =(x1, x2)))
		cout << b->toString(sig) << endl; // ≤(x1, x2)
		cout << p->toString(sig) << endl; // (∀x1, (∀x2, (≤(x1, x2) ↔ (<(x1, x2) ∨ =(x1, x2)))))

		cout << zero->toString(sig) << endl; // 0
		cout << one->toString(sig) << endl; // S(0)
		cout << two->toString(sig) << endl; // S(S(0))
		cout << one_one->toString(sig) << endl; // +(S(0), S(0))

		auto p_ = p->treeClone(all), a_ = a->treeClone(all);

		p_->replaceVariables({
			make_pair(1, one),
			make_pair(2, zero)
		}, all);

		cout << p_->toString(sig) << endl; // (∀x1, (∀x2, (≤(x1, x2) ↔ (<(x1, x2) ∨ =(x1, x2)))))

		a_->replaceVariables({
			make_pair(1, one),
			make_pair(2, one_one)
		}, all);

		cout << a_->toString(sig) << endl; // (≤(S(0), +(S(0), S(0))) ↔ (<(S(0), +(S(0), S(0))) ∨ =(S(0), +(S(0), S(0)))))

		auto x_y = newNode(Node::FUNCTION, all); x_y->function.id = MUL; x_y->attachChildren({ x, y }, all);

		cout << x_y->toString(sig) << endl; // *(x1, x2)

		a_->replacePropositions({
			make_pair(LEQUAL, b),
			make_pair(LESS, a)
		}, all);

		cout << a_->toString(sig) << endl; // (≤(x1, x2) ↔ ((≤(x1, x2) ↔ (<(x1, x2) ∨ =(x1, x2))) ∨ =(S(0), +(S(0), S(0)))))

		a_->replacePropositions({
			make_pair(LEQUAL, b),
			make_pair(LESS, a)
		}, all);

		cout << a_->toString(sig) << endl; // (≤(x1, x2) ↔ ((≤(x1, x2) ↔ ((≤(x1, x2) ↔ (<(x1, x2) ∨ =(x1, x2))) ∨ =(x1, x2))) ∨ =(S(0), +(S(0), S(0)))))

		a_->replaceVariables({
			make_pair(1, x_y),
			make_pair(2, two)
		}, all);

		cout << a_->toString(sig) << endl;
		// (≤(*(x1, x2), S(S(0))) ↔ ((≤(*(x1, x2), S(S(0))) ↔ ((≤(*(x1, x2), S(S(0)))
		// ↔ (<(*(x1, x2), S(S(0))) ∨ =(*(x1, x2), S(S(0))))) ∨ =(*(x1, x2), S(S(0))))) ∨ =(S(0), +(S(0), S(0)))))

		cout << zero->isForm(sig) << zero->isClosedForm(sig) << zero->isTerm(sig) << zero->isClosedTerm(sig) << endl; // 0011
		cout << two->isForm(sig) << two->isClosedForm(sig) << two->isTerm(sig) << two->isClosedTerm(sig) << endl; // 0011
		cout << one_one->isForm(sig) << one_one->isClosedForm(sig) << one_one->isTerm(sig) << one_one->isClosedTerm(sig) << endl; // 0011
		cout << x_y->isForm(sig) << x_y->isClosedForm(sig) << x_y->isTerm(sig) << x_y->isClosedTerm(sig) << endl; // 0010

		cout << p_->propositionIsFreeFor(a, LEQUAL) << p_->propositionIsFreeFor(p, LEQUAL) << endl; // 01
		cout << p_->variableIsFreeFor(x_y, 1) << endl; // 1
		cout << q->variableIsFreeFor(x_y, 1) << q->variableIsFreeFor(x_y, 2) << endl; // 01

		q->replaceVariables({ make_pair(1, x_y) }, all);
		cout << q->toString(sig) << endl; // (∀x2, (≤(*(x1, x2), x2) ↔ (<(*(x1, x2), x2) ∨ =(*(x1, x2), x2))))

		q->replaceVariables({ make_pair(1, x_y) }, all);
		cout << q->toString(sig) << endl; // (∀x2, (≤(*(*(x1, x2), x2), x2) ↔ (<(*(*(x1, x2), x2), x2) ∨ =(*(*(x1, x2), x2), x2))))

		auto q_ = q->treeClone(all);

		q->replaceVariables({ make_pair(2, x_y) }, all);
		cout << q->toString(sig) << endl; // (∀x2, (≤(*(*(x1, x2), x2), x2) ↔ (<(*(*(x1, x2), x2), x2) ∨ =(*(*(x1, x2), x2), x2))))

		auto malform = newNode(Node::FUNCTION, all); malform->function.id = ADD; malform->attachChildren({ x, y, y }, all);
		auto wellform = newNode(Node::FUNCTION, all); wellform->function.id = ADD; wellform->attachChildren({ x, y }, all);
		auto wellform2 = newNode(Node::FUNCTION, all); wellform2->function.id = ADD; wellform2->attachChildren({ x, y }, all);
		auto wellform3 = newNode(Node::FUNCTION, all); wellform3->function.id = MUL; wellform3->attachChildren({ x, y }, all);

		cout << malform->isTerm(sig) << wellform->isTerm(sig) << wellform2->isTerm(sig) << wellform3->isTerm(sig) << endl; // 0111
		cout << (*q_ == *q) << (*q == *q_) << (q->toString(sig) == q_->toString(sig)) << endl; // 111
		cout << (*malform == *wellform) << (*wellform == *malform) << endl; // 00
		cout << (*wellform == *wellform2) << (*wellform2 == *wellform) << endl; // 11
		cout << (*wellform == *wellform3) << (*wellform3 == *wellform) << endl; // 00
	}

	return 0;
}
*/
