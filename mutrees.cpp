// ApiMu/FOL verifier v0.1
// Licensed under Creative Commons CC0 (no copyright reserved, use at your will)

// This variant of FOL & ND is largely based on Dirk van Dalen's *Logic and Structure*...
// Additional features are described in `notes/design.md`.
// The code below may contain (many) errors. Will write another checker using a more suitable language (e.g. Haskell or Lean).

#include <iostream>
#include <stdio.h>
#include <initializer_list>
#include <vector>
#include <set>
#include <map>
#include <algorithm>
#include <string>
#include <sstream>

using std::vector;
using std::set;
using std::map;
using std::pair, std::make_pair;
using std::string;
using std::cin, std::cout, std::endl;

// Duplicates are allowed
template <typename T>
inline vector<T> set_union(const vector<T>& s1, const vector<T>& s2) {
	if (s1.size() < s2.size()) return set_union(s2, s1);
	vector<T> res = s1;
	for (const auto& x: s2) res.push_back(x);
	return res;
}

// All instances are removed
template <typename T>
inline vector<const T*> ptr_set_minus_elem(const vector<const T*>& s, const T* t) {
	vector<const T*> res;
	for (auto p: s) if (*p != *t) res.push_back(p);
	return res;
}

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

// Type; a pair of (tag, arity) is sufficient to represent all types in this language (except propositions)
typedef pair<unsigned int, unsigned int> Type;
// Context/signature; contains pairs of (type, name) where names are for readability only
typedef vector<pair<Type, string> > Context;

// Formula (schema) tree node, and related syntactic operations
// Pre (for all methods): there is no "cycle" throughout the tree
// Pre & invariant (for all methods): pointer is nonzero <=> pointer is valid (exception: root nodes have undefined *s pointer)
class Node {
public:
	// Alphabet for a first-order language with equality
	enum Symbol: unsigned int {
		EMPTY = 0, // For default values only. EMPTY nodes are not well-formed terms or formulas.
		VAR, FUNC, PRED,
		TRUE, FALSE, NOT, AND, OR, IMPLIES, IFF,
		FORALL, EXISTS, UNIQUE, FORALLFUNC, FORALLPRED
	} symbol;

	// Union-like classes: https://en.cppreference.com/w/cpp/language/union
	// The `id` field in VAR, FUNC, PRED stands for de Brujin index if the (meta)variable is not free
	// To improve readability, the "preferred" or "default" names for bound variables will also be stored for each formula;
	// The corresponding index is `quantifier.id`, which will NOT be used internally.
	union {
		// VAR, FUNC, PRED (`c` is ignored for VAR)
		struct { bool free; unsigned int id; Node* c; } atom;
		// TRUE, FALSE, NOT, AND, OR, IMPLIES, IFF (`l` is ignored for the first two; `r` is ignored for the first three)
		struct { Node* l, * r; } connective;
		// FORALL, EXISTS, UNIQUE, FORALLFUNC, FORALLPRED (`arity` is ignored for the first three)
		struct { unsigned int id, arity; Node* r; } quantifier;
	}; // 16B (64-bit)

	Node* s; // Next sibling (for children of PRED and FUNC nodes only)

	// Implicitly-defined default constructor does nothing: https://en.cppreference.com/w/cpp/language/default_constructor
	// The constructors below guarantee that all nonzero pointers (in the "active variant") are valid
	Node(): symbol(EMPTY), s(nullptr) {}
	Node(Symbol sym): symbol(sym), s(nullptr) {
		switch (sym) {
		case VAR: case FUNC: case PRED:
			atom.c = nullptr; break;
		case TRUE: case FALSE: case NOT: case AND: case OR: case IMPLIES: case IFF:
			connective.l = connective.r = nullptr; break;
		case FORALL: case EXISTS: case UNIQUE: case FORALLFUNC: case FORALLPRED:
			quantifier.r = nullptr; break;
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
	// Pre: symbol is FUNC of PRED; all nonzero pointers are valid
	unsigned int arity() const {
		if (symbol != FUNC && symbol != PRED) return 0;
		unsigned int res = 0;
		const Node* p = atom.c;
		while (p) p = p->s, res++;
		return res;
	}

	// Attach children (no-copy)
	// Each node may only be attached to **one** parent node at a time!
	// Pre: symbol is FUNC of PRED
	void attachChildrenUnsafe(const std::initializer_list<Node*>& nodes) {
		if (symbol != FUNC && symbol != PRED) return;
		Node* last = nullptr;
		for (Node* node: nodes) {
			(last? last->s : atom.c) = node;
			last = node;
		}
	}

	// Deep copy
	// Pre: all nonzero pointers are valid
	// O(size)
	Node* treeClone(Allocator<Node>& pool) const {
		Node* res = &pool.push_back(*this);
		switch (symbol) {
		case EMPTY: case VAR:
			break;
		case FUNC: case PRED: {
			const Node* p = atom.c;
			Node** last = &(res->atom.c);
			while (p) {
				// *p: next node to be copied
				// *last: the pointer that should be set to point to the copy
				Node* curr = p->treeClone(pool);
				*last = curr;
				last = &(curr->s);
				p = p->s;
			}
			}
			break;
		case TRUE: case FALSE: case NOT: case AND: case OR: case IMPLIES: case IFF:
			if (connective.l) res->connective.l = (connective.l)->treeClone(pool);
			if (connective.r) res->connective.r = (connective.r)->treeClone(pool);
			break;
		case FORALL: case EXISTS: case UNIQUE: case FORALLFUNC: case FORALLPRED:
			if (quantifier.r) res->quantifier.r = (quantifier.r)->treeClone(pool);
			break;
		}
		return res;
	}

	// Attach children (copies each node in the list)
	// Pre: symbol is FUNC of PRED
	void attachChildren(const std::initializer_list<const Node*>& nodes, Allocator<Node>& pool) {
		if (symbol != FUNC && symbol != PRED) return;
		Node* last = nullptr;
		for (const Node* cnode: nodes) {
			Node* node = cnode->treeClone(pool);
			(last? last->s : atom.c) = node;
			last = node;
		}
	}

	// Pre: symbol is NOT, FORALL, EXISTS, UNIQUE, FORALLFUNC or FORALLPRED
	void attach(const Node* c, Allocator<Node>& pool) {
		switch (symbol) {
		case NOT:
			connective.l = c->treeClone(pool); break;
		case FORALL: case EXISTS: case UNIQUE: case FORALLFUNC: case FORALLPRED:
			quantifier.r = c->treeClone(pool); break;
		}
	}

	// Pre: symbol is AND, OR, IMPLIES or IFF
	void attachL(const Node* c, Allocator<Node>& pool) {
		switch (symbol) {
		case AND: case OR: case IMPLIES: case IFF:
			connective.l = c->treeClone(pool); break;
		}
	}

	// Pre: symbol is AND, OR, IMPLIES or IFF
	void attachR(const Node* c, Allocator<Node>& pool) {
		switch (symbol) {
		case AND: case OR: case IMPLIES: case IFF:
			connective.r = c->treeClone(pool); break;
		}
	}

	// Check if the subtree is a well-formed term (cf. definition 2.3.1)
	// Pre: all nonzero pointers are valid
	// O(size)
	bool isTerm(const Context& ctx, const vector<Type>& stk) const {
		switch (symbol) {
		case VAR:
			if (atom.free) return atom.id < ctx.size() && ctx[atom.id].first            == Type(VAR, 0);
			else           return atom.id < stk.size() && stk[stk.size() - 1 - atom.id] == Type(VAR, 0);
		case FUNC: {
			const Node* p = atom.c;
			unsigned int arity = 0;
			while (p) {
				if (!p->isTerm(ctx, stk)) return false;
				p = p->s;
				arity++;
			}
			if (atom.free) return atom.id < ctx.size() && ctx[atom.id].first            == Type(FUNC, arity);
			else           return atom.id < stk.size() && stk[stk.size() - 1 - atom.id] == Type(FUNC, arity);
			}
		}
		return false;
	}

	// Check if the subtree is a well-formed formula (cf. definition 2.3.2)
	// Pre: all nonzero pointers are valid
	// Post: stk will be unchanged
	// O(size)
	bool isForm(const Context& ctx, vector<Type>& stk) const {
		switch (symbol) {
		case PRED: {
			const Node* p = atom.c;
			unsigned int arity = 0;
			while (p) {
				if (!p->isTerm(ctx, stk)) return false;
				p = p->s;
				arity++;
			}
			if (atom.free) return atom.id < ctx.size() && ctx[atom.id].first            == Type(PRED, arity);
			else           return atom.id < stk.size() && stk[stk.size() - 1 - atom.id] == Type(PRED, arity);
			}
		case TRUE: case FALSE:
			return true;
		case NOT:
			return connective.l && connective.l->isForm(ctx, stk);
		case AND: case OR: case IMPLIES: case IFF:
			return connective.l && connective.r && connective.l->isForm(ctx, stk) && connective.r->isForm(ctx, stk);
		case FORALL: case EXISTS: case UNIQUE: case FORALLFUNC: case FORALLPRED: {
			// Push the current binder onto the stack
			switch (symbol) {
			case FORALLFUNC: stk.push_back(Type(FUNC, quantifier.arity)); break;
			case FORALLPRED: stk.push_back(Type(PRED, quantifier.arity)); break;
			default:         stk.push_back(Type(VAR, 0));                 break;
			}
			// Check recursively
			bool res = quantifier.r && quantifier.r->isForm(ctx, stk);
			// Pop stack and return
			stk.pop_back();
			return res;
		}
		}
		return false;
	}

	// Syntactical equality
	// Pre: (*this) must be a well-formed term or formula
	// O(size)
	bool operator==(const Node& rhs) const {
		if (symbol != rhs.symbol) return false;
		// symbol == rhs.symbol
		switch (symbol) {
		case VAR: return atom.free == rhs.atom.free && atom.id == rhs.atom.id;
		case FUNC: case PRED: {
			if (atom.free != rhs.atom.free || atom.id != rhs.atom.id) return false;
			const Node* p = atom.c, * prhs = rhs.atom.c;
			while (p && prhs) {
				if (!(*p == *prhs)) return false;
				p = p->s; prhs = prhs->s;
			}
			if (p || prhs) return false; // Both pointers must be empty at the same time
			}
			return true;
		case TRUE: case FALSE:
			return true;
		case NOT:
			return *(connective.l) == *(rhs.connective.l);
		case AND: case OR: case IMPLIES: case IFF:
			return *(connective.l) == *(rhs.connective.l) && *(connective.r) == *(rhs.connective.r);
		case FORALL: case EXISTS: case UNIQUE:
			// (No need to compare quantifier.id, it serves to improve readability only!)
			return *(quantifier.r) == *(rhs.quantifier.r);
		case FORALLFUNC: case FORALLPRED:
			// (No need to compare quantifier.id, it serves to improve readability only!)
			return quantifier.arity == rhs.quantifier.arity && *(quantifier.r) == *(rhs.quantifier.r);
		}
		return false; // Unreachable
	}
	bool operator!=(const Node& rhs) const { return !(*this == rhs); }

	// Check if `i` is a free variable (cf. definitions 2.3.6, 2.3.7)
	// Pre: (*this) must be a well-formed term or formula
	// O(size)
	bool isFV(unsigned int i) const {
		switch (symbol) {
		case VAR:
			return atom.free && atom.id == i;
		case FUNC: case PRED: {
			const Node* p = atom.c;
			while (p) { if (p->isFV(i)) return true; p = p->s; }
			}
			return false;
		case TRUE: case FALSE:
			return false;
		case NOT:
			return connective.l->isFV(i);
		case AND: case OR: case IMPLIES: case IFF:
			return connective.l->isFV(i) || connective.r->isFV(i);
		case FORALL: case EXISTS: case UNIQUE: case FORALLFUNC: case FORALLPRED:
			return quantifier.r->isFV(i);
		}
		return false;
	}

/*
	// In-place simultaneous replacement of free variables by terms: s[t.../xi...] or φ[t.../xi...] (cf. definitions 2.3.9, 2.3.10)
	// The nodes given in the map will not be used directly; it will only be copied
	// Pre: (*this) must be a well-formed term or formula; t's must be well-formed terms
	// O(size * log(number of replacements))
	Node* replaceVariables(const map<unsigned int, const Node*>& reps, Allocator<Node>& pool) {
		switch (symbol) {
		case VAR: {
			auto it = reps.find(atom.id);
			if (it != reps.end()) return it->second->treeClone(pool);
			}
			break;
		case FUNCTION: case PREDICATE: {
			Node* p = (symbol == FUNCTION? function.c : predicate.c);
			Node** last = (symbol == FUNCTION? &function.c : &predicate.c);
			while (p) {
				// *p: next node to be processed
				// *last: the pointer that should be set to point to the new node
				Node* curr = p->replaceVariables(reps, pool); // replaceVariables() does not affect `p->s`
				*last = curr; // Does not affect `p->s`
				last = &(curr->s); // Does not affect `p->s`
				p = p->s;
			}
			}
			break;
		case ABSURDITY:
			break;
		case NEGATION:
			connective.l = connective.l->replaceVariables(reps, pool);
			break;
		case CONJUNCTION: case DISJUNCTION: case IMPLICATION: case EQUIVALENCE:
			connective.l = connective.l->replaceVariables(reps, pool);
			connective.r = connective.r->replaceVariables(reps, pool);
			break;
		case UNIVERSAL: case EXISTENTIAL: {
			auto it = reps.find(quantifier.l);
			if (it == reps.end()) quantifier.r = quantifier.r->replaceVariables(reps, pool);
			else {
				auto reps_ = reps;
				reps_.erase(quantifier.l);
				if (!reps_.empty()) quantifier.r = quantifier.r->replaceVariables(reps_, pool);
			}
			}
			break;
		}
		return this;
	}
	
	// In-place simultaneous replacement of predicates by formulas: φ[ψ.../$i...] (cf. definition 2.3.11)
	// The nodes given in the map will not be used directly; it will only be copied
	// Pre: (*this) must be a well-formed formula; ψ's must be well-formed formulas
	// O(size * log(number of replacements))
	Node* replacePropositions(const map<unsigned int, const Node*>& reps, Allocator<Node>& pool) {
		switch (symbol) {
		case CONSTANT: case VARIABLE: case FUNCTION:
			break;
		case PREDICATE: {
			auto it = reps.find(predicate.id);
			if (it != reps.end()) return it->second->treeClone(pool);
			}
			break;
		case ABSURDITY:
			break;
		case NEGATION:
			connective.l = connective.l->replacePropositions(reps, pool);
			break;
		case CONJUNCTION: case DISJUNCTION: case IMPLICATION: case EQUIVALENCE:
			connective.l = connective.l->replacePropositions(reps, pool);
			connective.r = connective.r->replacePropositions(reps, pool);
			break;
		case UNIVERSAL: case EXISTENTIAL:
			quantifier.r = quantifier.r->replacePropositions(reps, pool);
			break;
		}
		return this;
	}
*/

	// Print
	// Displays "[ERROR]" iff not a well-formed term / formula
	// Pre: all nonzero pointers are valid
	// Post: stk will be unchanged
	string toString(const Context& ctx, vector<pair<Type, string> >& stk, const vector<string>& boundNames) const {
		switch (symbol) {
		case VAR:
			if (atom.free) { if (atom.id < ctx.size() && ctx[atom.id].first                  == Type(VAR, 0)) return ctx[atom.id].second; }
			else           { if (atom.id < stk.size() && stk[stk.size() - 1 - atom.id].first == Type(VAR, 0)) return stk[stk.size() - 1 - atom.id].second; }
			break;
		case FUNC: case PRED: {
			string res;
			const Node* p = atom.c;
			unsigned int arity = 0;
			while (p) {
				res += " " + p->toString(ctx, stk, boundNames);
				p = p->s;
				arity++;
			}
			if (atom.free) { if (atom.id < ctx.size() && ctx[atom.id].first                  == Type(symbol, arity)) return "(" + ctx[atom.id].second + res + ")"; }
			else           { if (atom.id < stk.size() && stk[stk.size() - 1 - atom.id].first == Type(symbol, arity)) return "(" + stk[stk.size() - 1 - atom.id].second + res + ")"; }
			break;
			}
		case TRUE:
			return "⊤";
		case FALSE:
			return "⊥";
		case NOT:
			if (connective.l) return "¬" + connective.l->toString(ctx, stk, boundNames);
			break;
		case AND: case OR: case IMPLIES: case IFF:
			if (connective.l && connective.r) {
				string ch;
				switch (symbol) {
					case AND:     ch = " ∧ "; break;
					case OR:      ch = " ∨ "; break;
					case IMPLIES: ch = " → "; break;
					case IFF:     ch = " ↔ "; break;
				}
				return "(" + connective.l->toString(ctx, stk, boundNames) + ch + connective.r->toString(ctx, stk, boundNames) + ")";
			}
			break;
		case FORALL: case EXISTS: case UNIQUE: case FORALLFUNC: case FORALLPRED:
			if (quantifier.r && quantifier.id < boundNames.size()) {
				string ch, name = boundNames[quantifier.id], res;
				switch (symbol) {
					case FORALL:     ch = "∀ ";  break;
					case EXISTS:     ch = "∃ ";  break;
					case UNIQUE:     ch = "∃! "; break;
					case FORALLFUNC: ch = "∀# "; break;
					case FORALLPRED: ch = "∀$ "; break;
				}
				res = "(" + ch + name;
				// Push the current binder onto the stack
				switch (symbol) {
				case FORALLFUNC: stk.push_back(make_pair(Type(FUNC, quantifier.arity), name)); res += "/" + std::to_string(quantifier.arity); break;
				case FORALLPRED: stk.push_back(make_pair(Type(PRED, quantifier.arity), name)); res += "/" + std::to_string(quantifier.arity); break;
				default:         stk.push_back(make_pair(Type(VAR, 0),                 name));                                                break;
				}
				// Print recursively
				res += ", " + quantifier.r->toString(ctx, stk, boundNames) + ")";
				// Pop stack and return
				stk.pop_back();
				return res;
			}
			break;
		}
		return "[ERROR]";
	}

	// TODO: pretty print (infixl, infixr, precedence, etc.)
};

Node* newNode(Node::Symbol sym, Allocator<Node>& pool) {
	return &pool.push_back(Node(sym));
}

// (Non-context-changing) derivation tree node, and related syntactic operations
class Derivation {
public:
	// (Non-context-changing) Natural Deduction rules for classical FOL + equality + metavariables
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
		*/
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
				*(a->connective.l) == *l && *(a->connective.r) == *r)
				return { true, set_union(hyps[0], hyps[1]) };
			else return fail;
		}
		case CONJUNCTION_E: {
			if (c.size() != 1) return fail;
			const Node* p = c[0]->a;
			// One premise in the form of (l ∧ r), conclusion equals to l or r
			if (p->symbol == Node::CONJUNCTION &&
				(*a == *(p->connective.l) || *a == *(p->connective.r)))
				return { true, hyps[0] };
			else return fail;
		}
		case DISJUNCTION_I: {
			if (c.size() != 1) return fail;
			const Node* p = c[0]->a;
			// One premise p, conclusion in the form of (p ∨ r) or (l ∨ p)
			if (a->symbol == Node::DISJUNCTION &&
				(*(a->connective.l) == *p || *(a->connective.r) == *p))
				return { true, hyps[0] };
			else return fail;
		}
		case DISJUNCTION_E: {
			if (c.size() != 3) return fail;
			const Node *d = c[0]->a, *r0 = c[1]->a, *r1 = c[2]->a;
			// Three premises (p ∨ q), r, r, conclusion is r, cancelling hypotheses p, q in left, right
			if (d->symbol != Node::DISJUNCTION || *r0 != *r1) return fail;
			const Node *p = d->connective.l, *q = d->connective.r;
			if (*a == *r0)
				return { true, set_union(hyps[0],
				         set_union(ptr_set_minus_elem(hyps[1], p), ptr_set_minus_elem(hyps[2], q))) };
			else return fail;
		}
		case IMPLICATION_I: {
			if (c.size() != 1) return fail;
			const Node* p = c[0]->a;
			// One premise p, conclusion in the form of (q → p), cancelling hypothesis q
			if (a->symbol != Node::IMPLICATION || *(a->connective.r) != *p) return fail;
			const Node* q = a->connective.l;
			return { true, ptr_set_minus_elem(hyps[0], q) };
		}
		case IMPLICATION_E: {
			if (c.size() != 2) return fail;
			const Node *l = c[0]->a, *r = c[1]->a;
			// Two premises in the form of (p → q), p, conclusion is q
			if (l->symbol == Node::IMPLICATION &&
				(*r == *(l->connective.l) && *a == *(l->connective.r)))
				return { true, set_union(hyps[0], hyps[1]) };
			else return fail;
		}
		case NEGATION_I: {
			if (c.size() != 1) return fail;
			const Node* f = c[0]->a;
			// One premise ⊥, conclusion in the form of (¬p), cancelling hypothesis p
			if (a->symbol != Node::NEGATION || f->symbol != Node::ABSURDITY) return fail;
			const Node* p = a->connective.l;
			return { true, ptr_set_minus_elem(hyps[0], p) };
		}
		case NEGATION_E: {
			if (c.size() != 2) return fail;
			const Node *l = c[0]->a, *r = c[1]->a;
			// Two premises (¬p), p, conclusion is ⊥
			if (a->symbol != Node::ABSURDITY || l->symbol != Node::NEGATION) return fail;
			if (*r == *(l->connective.l))
				return { true, set_union(hyps[0], hyps[1]) };
			else return fail;
		}
		case EQUIVALENCE_I: {
			if (c.size() != 2) return fail;
			const Node *l = c[0]->a, *r = c[1]->a;
			// Two premises l, r, conclusion in the form of (l ↔ r), cancelling hypotheses r and l in left, right
			if (a->symbol != Node::EQUIVALENCE) return fail;
			if (*(a->connective.l) == *l && *(a->connective.r) == *r)
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
				const Node *li = pi->connective.l, *ri = pi->connective.r;
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
			if (*(p->connective.l) == *(a->connective.r) && *(p->connective.r) == *(a->connective.l))
				return { true, hyps[0] };
			else return fail;
		}
		case EQUIVALENCE_TRANS: {
			if (c.size() != 2) return fail;
			const Node *l = c[0]->a, *r = c[1]->a;
			// Two premises in the form of (p ↔ q), (q ↔ s), conclusion is (p ↔ s)
			if (l->symbol != Node::EQUIVALENCE || r->symbol != Node::EQUIVALENCE ||
				a->symbol != Node::EQUIVALENCE) return fail;
			const Node *p = l->connective.l, *q0 = l->connective.r;
			const Node *q1 = r->connective.l, *s = r->connective.r;
			if (*q0 == *q1 && *(a->connective.l) == *p && *(a->connective.r) == *s)
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
			Node t(Node::NEGATION); t.connective.l = a;
			return { true, ptr_set_minus_elem(hyps[0], &t) };
		}
		case UNIVERSAL_I: {
			if (c.size() != 1) return fail;
			const Node* p = c[0]->a;
			// One premise p, conclusion in the form of (∀xi, p), with xi does not occur free in any hypothesis
			if (a->symbol != Node::UNIVERSAL || *(a->quantifier.r) != *p) return fail;
			unsigned int i = a->quantifier.l;
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
			unsigned int i = p->quantifier.l;
			p = p->quantifier.r;
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
			unsigned int i = a->quantifier.l;
			const Node* q = a->quantifier.r;
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
			unsigned int i = p->quantifier.l;
			p = p->quantifier.r;
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
		p.quantifier.l = 1; q.quantifier.l = 2;
		Node a(Node::EQUIVALENCE), b(Node::PREDICATE), c(Node::DISJUNCTION), d(Node::PREDICATE), e(Node::PREDICATE);
		b.predicate.id = LEQUAL; d.predicate.id = LESS; e.predicate.id = EQUAL;
		Node x0(Node::VARIABLE), y0(Node::VARIABLE), x1(Node::VARIABLE), y1(Node::VARIABLE);
		Node x2(Node::VARIABLE), y2(Node::VARIABLE), x3(Node::VARIABLE), y3(Node::VARIABLE);
		x0.variable.id = x1.variable.id = x2.variable.id = x3.variable.id = 1;
		y0.variable.id = y1.variable.id = y2.variable.id = y3.variable.id = 2;

		cout << a.isTerm(sig) << a.isForm(sig) << e.isTerm(sig) << e.isForm(sig) << endl; // 0000
		a.connective.l = &b; a.connective.r = &c;
		cout << a.isForm(sig) << b.isForm(sig) << b.isTerm(sig) << endl; // 000
		b.attachChildrenUnsafe({ &x1, &y1 });
		cout << a.isForm(sig) << b.isForm(sig) << b.isTerm(sig) << endl; // 010
		c.connective.l = &d; c.connective.r = &e;
		cout << a.isForm(sig) << c.isForm(sig) << endl; // 00
		d.attachChildrenUnsafe({ &x2, &y2 });
		cout << a.isForm(sig) << c.isForm(sig) << endl; // 00
		e.attachChildrenUnsafe({ &x3, &y3 });
		cout << a.isForm(sig) << c.isForm(sig) << endl; // 11

		cout << b.toString(sig) << endl; // ≤(x1, x2)
		cout << a.toString(sig) << endl; // (≤(x1, x2) ↔ (<(x1, x2) ∨ =(x1, x2)))

		p.quantifier.r = &q; q.quantifier.r = &a;
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

		auto p = newNode(Node::UNIVERSAL, all); p->quantifier.l = 1;
		auto q = newNode(Node::UNIVERSAL, all); q->quantifier.l = 2;

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
