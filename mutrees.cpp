// MuTrees/FOL verifier v0.1
// This variant of FOL & ND is largely based on Dirk van Dalen's *Logic and Structure*...

// Author: Zhanrong Qiao
// Licensed under CC0

// The code below may contain (many) errors.

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

/*
template <typename T>
inline void set_union_inplace(vector<T>& dst, const vector<T>& rhs) {
	vector<T> t = dst;
	dst.resize(t.size() + rhs.size());
	size_t len = std::set_union(t.begin(), t.end(), rhs.begin(), rhs.end(), dst.begin()) - dst.begin();
	dst.resize(len);
}
*/

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

// Signature of a language (an "environment" that keeps track of all nonlogical symbols)
class Signature {
private:
	vector<string> fs, ps, cs; // Symbols for functions, predicates and constants
	vector<unsigned int> fa, pa; // Corresponding arities

public:
	size_t addFunction(string symbol, unsigned int arity) {
		fa.push_back(arity);
		fs.push_back(symbol);
		return fs.size() - 1u;
	}

	size_t addPredicate(string symbol, unsigned int arity) {
		pa.push_back(arity);
		ps.push_back(symbol);
		return ps.size() - 1u;
	}

	size_t addConstant(string symbol) {
		cs.push_back(symbol);
		return cs.size() - 1u;
	}

	unsigned int functionArity(size_t id) const { return fa[id]; }
	string functionSymbol(size_t id) const { return fs[id]; }
	unsigned int predicateArity(size_t id) const { return pa[id]; }
	string predicateSymbol(size_t id) const { return ps[id]; }
	string constantSymbol(size_t id) const { return cs[id]; }
	static string variableSymbol(size_t id) { std::stringstream ss; ss << "x" << id; return ss.str(); }
	static string formulaSymbol(size_t id) { std::stringstream ss; ss << "$" << id; return ss.str(); }
};

// Formula (schema) tree node, and related syntactic operations
// Pre (for all methods): there is no "cycle" throughout the tree
class Node {
public:
	// Alphabet for a first-order language with equality
	enum Symbol: unsigned int {
		EMPTY = 0, // For default values only. EMPTY nodes are not well-formed terms or formulas.
		CONSTANT, VARIABLE, FUNCTION, PREDICATE, // EQUALS,
		ABSURDITY, NEGATION, CONJUNCTION, DISJUNCTION, IMPLICATION, EQUIVALENCE,
		UNIVERSAL, EXISTENTIAL,
	} symbol;
	
	// Union-like classes: https://en.cppreference.com/w/cpp/language/union
	union {
		struct { unsigned int id; } constant;
		struct { unsigned int id; } variable;
		struct { unsigned int id; Node* c; } function;
		struct { unsigned int id; Node* c; } predicate;
		struct { Node *l, *r; } connective; // 16B (64-bit)
		struct { unsigned int l; Node* r; } quantifier;
	};
	
	Node* s; // Next sibling (for children of PREDICATE and FUNCTION nodes only)

	// Storage: 4B + 8B + 4B = 16B (32-bit) / 4B + 16B + 8B = 28B (32B after alignment?) (64-bit)
	// Assuming: pointer is nonzero <=> pointer is valid (exception: root nodes have undefined *s pointer)

	// Implicitly-defined default constructor does nothing: https://en.cppreference.com/w/cpp/language/default_constructor
	Node(): symbol(EMPTY), s(nullptr) {}
	Node(Symbol sym): symbol(sym), s(nullptr) {
		switch (sym) {
		case CONSTANT: constant.id = 0; break;
		case VARIABLE: variable.id = 0; break;
		case FUNCTION: function.id = 0; function.c = nullptr; break;
		case PREDICATE: predicate.id = 0; predicate.c = nullptr; break;
		case ABSURDITY: case NEGATION: case CONJUNCTION: case DISJUNCTION: case IMPLICATION: case EQUIVALENCE:
			connective.l = connective.r = nullptr; break;
		case UNIVERSAL: case EXISTENTIAL: quantifier.l = 0; quantifier.r = nullptr; break;
		}
	};
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
	
	// Arity "de facto"
	// Pre: all nonzero pointers are valid
	unsigned int arity() const {
		if (symbol != FUNCTION && symbol != PREDICATE) return 0;
		unsigned int res = 0;
		const Node* p = (symbol == FUNCTION? function.c : predicate.c);
		while (p) p = p->s, res++;
		return res;
	}

	// Attach children (no-copy)
	// Each node may only be attached to **one** parent node at a time!
	// Pre: symbol is FUNCTION of PREDICATE
	void attachChildrenNoCopy(const std::initializer_list<Node*>& nodes) {
		if (symbol != FUNCTION && symbol != PREDICATE) return;
		Node* last = nullptr;
		for (Node* node: nodes) {
			if (last) last->s = node;
			else (symbol == FUNCTION? function.c : predicate.c) = node;
			last = node;
		}
	}

	// Deep copy
	// Pre: all nonzero pointers are valid
	// O(size)
	Node* treeClone(Allocator<Node>& pool) const {
		Node* res = &pool.push_back(*this);
		switch (symbol) {
		case EMPTY: case CONSTANT: case VARIABLE:
			break;
		case FUNCTION: case PREDICATE: {
			const Node* p = (symbol == FUNCTION? function.c : predicate.c);
			Node** last = (symbol == FUNCTION? &(res->function.c) : &(res->predicate.c));
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
		case ABSURDITY: case NEGATION: case CONJUNCTION: case DISJUNCTION: case IMPLICATION: case EQUIVALENCE:
			if (connective.l) res->connective.l = (connective.l)->treeClone(pool);
			if (connective.r) res->connective.r = (connective.r)->treeClone(pool);
			break;
		case UNIVERSAL: case EXISTENTIAL:
			if (quantifier.r) res->quantifier.r = (quantifier.r)->treeClone(pool);
			break;
		}
		return res;
	}

	// (Strict) equality
	// Pre: all nonzero pointers are valid
	// O(size)
	bool operator==(const Node& rhs) const {
		if (symbol != rhs.symbol) return false;
		// symbol == rhs.symbol
		switch (symbol) {
		case EMPTY: return true;
		case CONSTANT: return constant.id == rhs.constant.id;
		case VARIABLE: return variable.id == rhs.variable.id;
		case FUNCTION: case PREDICATE: {
			const Node *p, *prhs;
			if (symbol == FUNCTION) {
				if (function.id != rhs.function.id) return false;
				p = function.c;
				prhs = rhs.function.c;
			} else {
				if (predicate.id != rhs.predicate.id) return false;
				p = predicate.c;
				prhs = rhs.predicate.c;
			}
			while (p && prhs) {
				if (!(*p == *prhs)) return false;
				p = p->s;
				prhs = prhs->s;
			}
			if (p || prhs) return false; // Both pointers must be empty at the same time
			}
			return true;
		case ABSURDITY: case NEGATION: case CONJUNCTION: case DISJUNCTION: case IMPLICATION: case EQUIVALENCE:
			if (connective.l && rhs.connective.l) {
				if (!(*(connective.l) == *(rhs.connective.l))) return false;
			} else if (connective.l || rhs.connective.l) return false;
			if (connective.r && rhs.connective.r) {
				if (!(*(connective.r) == *(rhs.connective.r))) return false;
			} else if (connective.r || rhs.connective.r) return false;
			return true;
		case UNIVERSAL: case EXISTENTIAL:
			if (quantifier.l != rhs.quantifier.l) return false;
			if (quantifier.r && rhs.quantifier.r) {
				if (!(*(quantifier.r) == *(rhs.quantifier.r))) return false;
			} else if (quantifier.r || rhs.quantifier.r) return false;
			return true;
		}
		return false; // Unreachable
	}
	bool operator!=(const Node& rhs) const { return !(*this == rhs); }

	// Attach children (copies each node in the list)
	// Pre: symbol is FUNCTION of PREDICATE
	void attachChildren(const std::initializer_list<const Node*>& nodes, Allocator<Node>& pool) {
		if (symbol != FUNCTION && symbol != PREDICATE) return;
		Node* last = nullptr;
		for (const Node* cnode: nodes) {
			Node* node = cnode->treeClone(pool);
			if (last) last->s = node;
			else (symbol == FUNCTION? function.c : predicate.c) = node;
			last = node;
		}
	}

	// Pre: symbol is NEGATION, UNIVERSAL or EXISTENTIAL
	void attach(const Node* c, Allocator<Node>& pool) {
		switch (symbol) {
		case NEGATION: connective.l = c->treeClone(pool); break;
		case UNIVERSAL: case EXISTENTIAL: quantifier.r = c->treeClone(pool); break;
		}
	}

	// Pre: symbol is CONJUNCTION, DISJUNCTION, IMPLICATION or EQUIVALENCE
	void attachL(const Node* c, Allocator<Node>& pool) {
		switch (symbol) {
		case CONJUNCTION: case DISJUNCTION: case IMPLICATION: case EQUIVALENCE:
			connective.l = c->treeClone(pool);
			break;
		}
	}

	// Pre: symbol is CONJUNCTION, DISJUNCTION, IMPLICATION or EQUIVALENCE
	void attachR(const Node* c, Allocator<Node>& pool) {
		switch (symbol) {
		case CONJUNCTION: case DISJUNCTION: case IMPLICATION: case EQUIVALENCE:
			connective.r = c->treeClone(pool);
			break;
		}
	}

	// Check if the subtree is a well-formed term (cf. definition 2.3.1)
	// Pre: all nonzero pointers are valid
	// O(size)
	bool isTerm(const Signature& sig) const {
		if (symbol == CONSTANT || symbol == VARIABLE) return true;
		if (symbol == FUNCTION) {
			const Node* p = function.c;
			unsigned int arity = 0;
			while (p) {
				if (!p->isTerm(sig)) return false;
				p = p->s;
				arity++;
			}
			return arity == sig.functionArity(function.id); // Check if the arity is correct
		}
		return false;
	}

	// Check if the subtree is a well-formed formula (cf. definition 2.3.2)
	// Pre: all nonzero pointers are valid
	// O(size)
	bool isForm(const Signature& sig) const {
		if (symbol == PREDICATE) {
			const Node* p = predicate.c;
			unsigned int arity = 0;
			while (p) {
				if (!p->isTerm(sig)) return false;
				p = p->s;
				arity++;
			}
			return arity == sig.predicateArity(predicate.id); // Check if the arity is correct
		}
		if (symbol == ABSURDITY && !connective.l && !connective.r) return true;
		if (symbol == NEGATION && (connective.l && connective.l->isForm(sig)) && !connective.r) return true;
		if ((symbol == CONJUNCTION || symbol == DISJUNCTION || symbol == IMPLICATION || symbol == EQUIVALENCE)
			&& (connective.l && connective.l->isForm(sig)) && (connective.r && connective.r->isForm(sig))) return true;
		if ((symbol == UNIVERSAL || symbol == EXISTENTIAL) && (quantifier.r && quantifier.r->isForm(sig))) return true;
		return false;
	}

	// Returns the set of free variables (cf. definitions 2.3.6, 2.3.7)
	// Pre: subtree must be a well-formed term or formula
	// O(size * log(number of vars))
	set<unsigned int> FV() const {
		set<unsigned int> res, upperbv;
		FV_(res, upperbv);
		return res;
	}

private:

	void FV_(set<unsigned int>& res, set<unsigned int>& upperbv) const {
		switch (symbol) {
		case CONSTANT:
			break;
		case VARIABLE:
			if (upperbv.find(variable.id) == upperbv.end()) res.insert(variable.id); // Insert if not bound
			break;
		case FUNCTION: case PREDICATE: {
			const Node* p = (symbol == FUNCTION? function.c : predicate.c);
			while (p) {
				p->FV_(res, upperbv);
				p = p->s;
			}
			}
			break;
		case ABSURDITY:
			break;
		case NEGATION:
			if (connective.l) connective.l->FV_(res, upperbv);
			break;
		case CONJUNCTION: case DISJUNCTION: case IMPLICATION: case EQUIVALENCE:
			if (connective.l) connective.l->FV_(res, upperbv);
			if (connective.r) connective.r->FV_(res, upperbv);
			break;
		case UNIVERSAL: case EXISTENTIAL:
			bool modified = upperbv.insert(quantifier.l).second;
			if (quantifier.r) quantifier.r->FV_(res, upperbv);
			if (modified) upperbv.erase(quantifier.l);
			break;
		}
	}
	
public:

	// Returns the set of bound variables (cf. definitions 2.3.6, 2.3.7)
	// Pre: subtree must be a well-formed term or formula
	// O(size * log(number of vars))
	set<unsigned int> BV() const {
		set<unsigned int> res;
		BV_(res);
		return res;
	}

private:

	void BV_(set<unsigned int>& res) const {
		switch (symbol) {
		case CONSTANT: case VARIABLE:
			break;
		case FUNCTION: case PREDICATE: {
			const Node* p = (symbol == FUNCTION? function.c : predicate.c);
			while (p) {
				p->BV_(res);
				p = p->s;
			}
			}
			break;
		case ABSURDITY:
			break;
		case NEGATION:
			if (connective.l) connective.l->BV_(res);
			break;
		case CONJUNCTION: case DISJUNCTION: case IMPLICATION: case EQUIVALENCE:
			if (connective.l) connective.l->BV_(res);
			if (connective.r) connective.r->BV_(res);
			break;
		case UNIVERSAL: case EXISTENTIAL:
			res.insert(quantifier.l);
			if (quantifier.r) quantifier.r->BV_(res);
			break;
		}
	}

public:

	// (cf. definitions 2.3.8)
	// Pre: subtree must be a well-formed term or formula
	bool isClosedTerm(const Signature& sig) { return isTerm(sig) && FV().empty(); }
	bool isClosedForm(const Signature& sig) { return isForm(sig) && FV().empty(); }
	
	// In-place simultaneous replacement of variables by terms: s[t.../xi...] or φ[t.../xi...] (cf. definitions 2.3.9, 2.3.10)
	// Pre: subtree must be a well-formed term or formula; t's must be well-formed terms; every individual input must be disjoint subtrees
	// Post: the nodes given in the map will not be used directly; it will only be copied
	// O(size * log(number of replacements))
	Node* replaceVariables(const map<unsigned int, const Node*>& reps, Allocator<Node>& pool) {
		switch (symbol) {
		case CONSTANT:
			break;
		case VARIABLE: {
			auto it = reps.find(variable.id);
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
			if (connective.l) connective.l = connective.l->replaceVariables(reps, pool);
			break;
		case CONJUNCTION: case DISJUNCTION: case IMPLICATION: case EQUIVALENCE:
			if (connective.l) connective.l = connective.l->replaceVariables(reps, pool);
			if (connective.r) connective.r = connective.r->replaceVariables(reps, pool);
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
	// Pre: subtree must be a well-formed formula; ψ's must be well-formed formulas; every individual input must be disjoint subtrees
	// Post: the nodes given in the map will not be used directly; it will only be copied
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
			if (connective.l) connective.l = connective.l->replacePropositions(reps, pool);
			break;
		case CONJUNCTION: case DISJUNCTION: case IMPLICATION: case EQUIVALENCE:
			if (connective.l) connective.l = connective.l->replacePropositions(reps, pool);
			if (connective.r) connective.r = connective.r->replacePropositions(reps, pool);
			break;
		case UNIVERSAL: case EXISTENTIAL:
			if (quantifier.r) quantifier.r = quantifier.r->replacePropositions(reps, pool);
			break;
		}
		return this;
	}

	// Check whether t is "free for" xi in this subtree (cf. definition 2.3.12, lemma 2.3.13)
	// Pre: subtree must be a well-formed term or formula
	// O(size * log(size of FV(t)))
	bool variableIsFreeFor(const Node* t, unsigned int i) const { return variableIsFreeFor_(t->FV(), i).first; }
	
private:

	// Returns: (current result, whether a replacement will occur in subtree)
	pair<bool, bool> variableIsFreeFor_(const set<unsigned int>& fvt, unsigned int i) const {
		switch (symbol) {
		case CONSTANT: break;
		case VARIABLE: return make_pair(true, variable.id == i);
		case FUNCTION: case PREDICATE: {
			bool replaced = false;
			const Node* p = (symbol == FUNCTION? function.c : predicate.c);
			while (p) {
				if (p->variableIsFreeFor_(fvt, i).second) replaced = true;
				p = p->s;
			}
			return make_pair(true, replaced);
			}
		case ABSURDITY: break;
		case NEGATION:
			if (!connective.l) break;
			return connective.l->variableIsFreeFor_(fvt, i);
		case CONJUNCTION: case DISJUNCTION: case IMPLICATION: case EQUIVALENCE: {
			if (!connective.l || !connective.r) break;
			pair<bool, bool> lres = connective.l->variableIsFreeFor_(fvt, i);
			pair<bool, bool> rres = connective.r->variableIsFreeFor_(fvt, i);
			return make_pair(lres.first && rres.first, lres.second || rres.second);
			}
		case UNIVERSAL: case EXISTENTIAL: {
			if (!quantifier.r || quantifier.l == i) break; // No replacement occurs in tree
			pair<bool, bool> rres = quantifier.r->variableIsFreeFor_(fvt, i);
			bool ok = ((!rres.second || fvt.find(quantifier.l) == fvt.end()) && rres.first);
			bool replaced = rres.second;
			return make_pair(ok, replaced);
			}
		}
		return make_pair(true, false); // When no replacement occurs in tree
	}

public:

	// Check whether ψ is "free for" $i in this subtree (cf. definition 2.3.14, lemma 2.3.15)
	// Pre: subtree must be a well-formed formula
	// O(size * log(size of FV(ψ)))
	bool propositionIsFreeFor(const Node* psi, unsigned int i) const { return propositionIsFreeFor_(psi->FV(), i).first; }

private:

	// Returns: (current result, whether a replacement will occur in subtree)
	pair<bool, bool> propositionIsFreeFor_(const set<unsigned int>& fvpsi, unsigned int i) const {
		switch (symbol) {
		case CONSTANT: case VARIABLE: case FUNCTION: break;
		case PREDICATE: return make_pair(true, predicate.id == i);
		case ABSURDITY: break;
		case NEGATION:
			if (!connective.l) break;
			return connective.l->propositionIsFreeFor_(fvpsi, i);
		case CONJUNCTION: case DISJUNCTION: case IMPLICATION: case EQUIVALENCE: {
			if (!connective.l || !connective.r) break;
			pair<bool, bool> lres = connective.l->propositionIsFreeFor_(fvpsi, i);
			pair<bool, bool> rres = connective.r->propositionIsFreeFor_(fvpsi, i);
			return make_pair(lres.first && rres.first, lres.second || rres.second);
			}
		case UNIVERSAL: case EXISTENTIAL: {
			if (!quantifier.r) break; // No replacement occurs in tree
			pair<bool, bool> rres = quantifier.r->propositionIsFreeFor_(fvpsi, i);
			bool ok = ((!rres.second || fvpsi.find(quantifier.l) == fvpsi.end()) && rres.first);
			bool replaced = rres.second;
			return make_pair(ok, replaced);
			}
		}
		return make_pair(true, false); // When no replacement occurs in tree
	}

public:

	// Print
	// Displays "[ERROR]" if not a well-formed term / formula
	string toString(const Signature& sig) const {
		switch (symbol) {
		case CONSTANT: return sig.constantSymbol(constant.id);
		case VARIABLE: return sig.variableSymbol(variable.id);
		case FUNCTION: case PREDICATE: {
			string res = (symbol == FUNCTION? sig.functionSymbol(function.id) : sig.predicateSymbol(predicate.id));
			res += "(";
			const Node* p = (symbol == FUNCTION? function.c : predicate.c);
			unsigned int arity = 0;
			while (p) {
				res += p->toString(sig);
				p = p->s;
				if (p) res += ", ";
				arity++;
			}
			res += ")";
			if (arity != (symbol == FUNCTION? sig.functionArity(function.id) : sig.predicateArity(predicate.id))) break;
			return res;
			}
		case ABSURDITY: return "⊥";
		case NEGATION: if (!connective.l) break; return "(¬" + connective.l->toString(sig) + ")";
		case CONJUNCTION: if (!connective.l || !connective.r) break; return "(" + connective.l->toString(sig) + " ∧ " + connective.r->toString(sig) + ")";
		case DISJUNCTION: if (!connective.l || !connective.r) break; return "(" + connective.l->toString(sig) + " ∨ " + connective.r->toString(sig) + ")";
		case IMPLICATION: if (!connective.l || !connective.r) break; return "(" + connective.l->toString(sig) + " → " + connective.r->toString(sig) + ")";
		case EQUIVALENCE: if (!connective.l || !connective.r) break; return "(" + connective.l->toString(sig) + " ↔ " + connective.r->toString(sig) + ")";
		case UNIVERSAL: if (!quantifier.r) break; return "(∀" + sig.variableSymbol(quantifier.l) + ", " + quantifier.r->toString(sig) + ")";
		case EXISTENTIAL: if (!quantifier.r) break;	return "(∃" + sig.variableSymbol(quantifier.l) + ", " + quantifier.r->toString(sig) + ")";
		}
		return "[ERROR]";
	}

	// TODO: pretty print
};

Node* newNode(Node::Symbol sym, Allocator<Node>& pool) {
	return &pool.push_back(Node(sym));
}

// Derivation (schema) tree node, and related syntactic operations
class Derivation {
public:
	// Natural Deduction rule names for classical FOL + equality
	enum Rule: unsigned int {
		CONJUNCTION_I, CONJUNCTION_E,
		DISJUNCTION_I, DISJUNCTION_E,
		IMPLICATION_I, IMPLICATION_E,
		NEGATION_I, NEGATION_E,
		EQUIVALENCE_I, EQUIVALENCE_E,
		EFQ, RAA,
		UNIVERSAL_I, UNIVERSAL_E,
		EXISTENTIAL_I, EXISTENTIAL_E,
		EQUALITY_I, EQUALITY_E, // Equality
		EQUALITY_SYMM, EQUALITY_TRANS, // Derived rules for equality
	} const rule;

	// Conclusion
	Node* a;

	// Child derivations
	// DAGs are allowed (used in Fitch-style notation)
	vector<Derivation*> c;

	// Storage: 4B + 4B + ?B = ?B (32-bit) / 4B + 8B + ?B = ?B (64-bit)
	// Assuming: pointer is present <=> pointer is valid

	// Implicitly-defined default constructor does nothing...
	Derivation(Rule r): rule(r), a(nullptr) {};

	// Arity "de facto"
	unsigned int arity() const { return c.size(); }

	// DAGs are allowed: each node may be attached to multiple parent nodes at a time
	void attachChildren(const std::initializer_list<Derivation*>& nodes) {
		for (Derivation* node: nodes) c.push_back(node);
	}

	// Check if a derivation is valid, given a set of axioms (cf. definitions in 1.4, 1.6, 2.8 and 2.9)
	// TODO: use hash tables to accelerate lookup
	bool check(const vector<const Node*>& hyp, const Signature& sig) {
		auto res = check_(sig);
		if (!res.first) return false;
		for (auto p: res.second) {
			bool found = false;
			for (auto q: hyp) {
				if (*p == *q) {
					found = true;
					break;
				}
			}
			if (!found) return false;
		}
		return true;
	}

private:

	// Returns: (current result, the set of uncancelled hypotheses)
	pair<bool, set<const Node*> > check_(const Signature& sig) {
		set<const Node*> hyps, empty;
		// Check if conclusion is wff
		if (!a->isForm(sig)) return make_pair(false, empty); 
		// Check all premises
		for (auto p: c) {
			auto res = p->check_(sig);
			if (!res.first) return make_pair(false, empty);
			if (hyps.empty()) hyps = res.second;
			else hyps.insert(res.second.begin(), res.second.end());
		}
		// Natural Deduction rules
		switch (rule) {
		case CONJUNCTION_I:
			if (c.size() != 2) return make_pair(false, empty);
			const Node *l = c[0]->a, *r = c[1]->a;
			// Two premises l and r, conclusion in the form of (l /\ r) or (r /\ l)
			return make_pair(a->symbol == Node::CONJUNCTION &&
				((*(a->connective.l) == *l && *(a->connective.r) == *r) ||
				 (*(a->connective.l) == *r && *(a->connective.r) == *l)),
				hyps);
		case CONJUNCTION_E:
			if (c.size() != 1) return make_pair(false, empty);
			const Node* p = c[0]->a;
			// One premise in the form of (l /\ r), conclusion equals to l or r
			return make_pair(p->symbol == Node::CONJUNCTION &&
				(*a == *(p->connective.l) || *a == *(p->connective.r)),
				hyps);
		case DISJUNCTION_I:
			if (c.size() != 1) return make_pair(false, empty);
			const Node* p = c[0]->a;
			// One premise p, conclusion in the form of (p \/ r) or (l \/ p)
			return make_pair(a->symbol == Node::DISJUNCTION &&
				(*(a->connective.l) == *p || (*(a->connective.r) == *p)),
				hyps);
		case DISJUNCTION_E:
		case IMPLICATION_I:
			// #####
		case IMPLICATION_E:
		case NEGATION_I:
		case NEGATION_E:
		case EQUIVALENCE_I:
		case EQUIVALENCE_E:
		case EFQ:
		case RAA:
		case UNIVERSAL_I:
		case UNIVERSAL_E:
		case EXISTENTIAL_I:
		case EXISTENTIAL_E:
		case EQUALITY_I:
		case EQUALITY_E:
		case EQUALITY_SYMM:
		case EQUALITY_TRANS:
		}
		return make_pair(false, empty); // Unreachable
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
			AXIOM_D, // Declaration of an axiom (schema)
			AXIOM_U, // Removal of an axiom (schema)
			PREDICATE_D, FUNCTION_D, // Extension by definitions (using "shorthands")
			FUNCTION_DD, // Extension by definitions (using "definite descriptions")
			PREDICATE_U, FUNCTION_U, // Undefining predicates and functions
			DERIVATION // A derivation to be checked
		} const id;

		// #####
	};

	// #####
};

// TODO: read binary files

int main() {
	
	{ // Experiment 1
		Signature sig;
		const unsigned int ZERO = sig.addConstant("0");
		const unsigned int ADD = sig.addFunction("+", 2);
		const unsigned int MUL = sig.addFunction("*", 2);
		const unsigned int SUCC = sig.addFunction("S", 1);
		const unsigned int EQUAL = sig.addPredicate("=", 2);
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
		b.attachChildrenNoCopy({ &x1, &y1 });
		cout << a.isForm(sig) << b.isForm(sig) << b.isTerm(sig) << endl; // 010
		c.connective.l = &d; c.connective.r = &e;
		cout << a.isForm(sig) << c.isForm(sig) << endl; // 00
		d.attachChildrenNoCopy({ &x2, &y2 });
		cout << a.isForm(sig) << c.isForm(sig) << endl; // 00
		e.attachChildrenNoCopy({ &x3, &y3 });
		cout << a.isForm(sig) << c.isForm(sig) << endl; // 11

		cout << b.toString(sig) << endl; // ≤(x1, x2)
		cout << a.toString(sig) << endl; // (≤(x1, x2) ↔ (<(x1, x2) ∨ =(x1, x2)))

		p.quantifier.r = &q; q.quantifier.r = &a;
		cout << p.toString(sig) << endl; // (∀x1, (∀x2, (≤(x1, x2) ↔ (<(x1, x2) ∨ =(x1, x2)))))

		cout << a.FV().size() << a.BV().size() << endl; // 20
		cout << q.FV().size() << q.BV().size() << endl; // 11
		cout << p.FV().size() << p.BV().size() << endl; // 02
	}

	{ // Experiment 2
		Signature sig;
		const unsigned int ZERO = sig.addConstant("0");
		const unsigned int ADD = sig.addFunction("+", 2);
		const unsigned int MUL = sig.addFunction("*", 2);
		const unsigned int SUCC = sig.addFunction("S", 1);
		const unsigned int EQUAL = sig.addPredicate("=", 2);
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
