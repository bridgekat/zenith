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

// Signature of a language (an "environment" that keeps track of all nonlogical symbols)
class Signature {
private:
	vector<string> fs, ps, cs; // Symbols for functions, predicates and constants
	vector<unsigned int> fa, pa; // Corresponding arities

public:
	// Predicate 0 is reserved for equality
	Signature() { addPredicate("=", 2); }

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
		CONSTANT, VARIABLE, FUNCTION, PREDICATE,
		ABSURDITY, NEGATION, CONJUNCTION, DISJUNCTION, IMPLICATION, EQUIVALENCE,
		UNIVERSAL, EXISTENTIAL,
	} symbol;
	
	// Union-like classes: https://en.cppreference.com/w/cpp/language/union
	union {
		struct { unsigned int id; } constant;
		struct { unsigned int id; } variable;
		struct { int id; Node* c; } function;  // Negative indices denote metavariables
		struct { int id; Node* c; } predicate; // Negative indices denote metavariables
		struct { Node *l, *r; } connective; // 16B (64-bit)
		struct { unsigned int l; Node* r; } quantifier;
	};
	
	Node* s; // Next sibling (for children of PREDICATE and FUNCTION nodes only)

	// Storage: 4B + 8B + 4B = 16B (32-bit) / 4B + 16B + 8B = 28B (32B after alignment?) (64-bit)
	// Assuming: pointer is nonzero <=> pointer is valid (exception: root nodes have undefined *s pointer)

	// Implicitly-defined default constructor does nothing: https://en.cppreference.com/w/cpp/language/default_constructor
	// The constructors below guarantee that all nonzero pointers (in the "active variant") are valid
	Node(): symbol(EMPTY), s(nullptr) {}
	Node(Symbol sym): symbol(sym), s(nullptr) {
		switch (sym) {
		case EMPTY: break;
		case CONSTANT: constant.id = 0; break;
		case VARIABLE: variable.id = 0; break;
		case FUNCTION: function.id = 0; function.c = nullptr; break;
		case PREDICATE: predicate.id = 0; predicate.c = nullptr; break;
		case ABSURDITY: case NEGATION: case CONJUNCTION: case DISJUNCTION: case IMPLICATION: case EQUIVALENCE:
			connective.l = connective.r = nullptr; break;
		case UNIVERSAL: case EXISTENTIAL: quantifier.l = 0; quantifier.r = nullptr; break;
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
	// Pre: symbol is FUNCTION of PREDICATE; all nonzero pointers are valid
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
	void attachChildrenUnsafe(const std::initializer_list<Node*>& nodes) {
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

	// Syntactical equality
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
	// Pre: (*this) must be a well-formed term or formula
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
	// Pre: (*this) must be a well-formed term or formula
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

	// Test if x_i is a free variable (cf. definitions 2.3.6, 2.3.7)
	// Pre: (*this) must be a well-formed term or formula
	// O(size)
	bool isFV(unsigned int i) const {
		switch (symbol) {
		case CONSTANT: return false;
		case VARIABLE: return variable.id == i;
		case FUNCTION: case PREDICATE: {
			const Node* p = (symbol == FUNCTION? function.c : predicate.c);
			while (p) { if (p->isFV(i)) return true; p = p->s; }
			}
			return false;
		case ABSURDITY: return false;
		case NEGATION: case CONJUNCTION: case DISJUNCTION: case IMPLICATION: case EQUIVALENCE:
			return (connective.l && connective.l->isFV(i)) ||
			       (connective.r && connective.r->isFV(i));
		case UNIVERSAL: case EXISTENTIAL:
			return quantifier.l != i && quantifier.r && quantifier.r->isFV(i);
		}
		return false;
	}

	// Check if (*this) is a closed term or formula (cf. definitions 2.3.8)
	// Pre: (*this) must be a well-formed term or formula
	bool isClosedTerm(const Signature& sig) { return isTerm(sig) && FV().empty(); }
	bool isClosedForm(const Signature& sig) { return isForm(sig) && FV().empty(); }
	
	// In-place simultaneous replacement of variables by terms: s[t.../xi...] or φ[t.../xi...] (cf. definitions 2.3.9, 2.3.10)
	// The nodes given in the map will not be used directly; it will only be copied
	// Pre: (*this) must be a well-formed term or formula; t's must be well-formed terms
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
	// Pre: (*this) must be a well-formed term or formula
	// O(size * log(size of FV(t)))
	bool variableIsFreeFor(const Node* t, unsigned int i) const { return variableIsFreeFor_(t->FV(), i).first; }
	bool variableIsFreeFor(const set<unsigned int>& fvt, unsigned int i) const { return variableIsFreeFor_(fvt, i).first; }
	
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
	// Pre: (*this) must be a well-formed formula
	// O(size * log(size of FV(ψ)))
	bool propositionIsFreeFor(const Node* psi, unsigned int i) const { return propositionIsFreeFor_(psi->FV(), i).first; }
	bool propositionIsFreeFor(const set<unsigned int>& fvpsi, unsigned int i) const { return propositionIsFreeFor_(fvpsi, i).first; }

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
	// Natural Deduction rules for classical FOL + equality
	// ("Derived rules" are marked for destruction!)
	enum Rule: unsigned int {
		EMPTY = 0,
		THEOREM, ASSUMPTION,
		PREDICATE_S, FUNCTION_S, // Specialization of metavariables
		CONJUNCTION_I, CONJUNCTION_E,
		DISJUNCTION_I, DISJUNCTION_E,
		IMPLICATION_I, IMPLICATION_E,
		NEGATION_I, NEGATION_E,
		EQUIVALENCE_I, EQUIVALENCE_E,
		EQUIVALENCE_SYMM, EQUIVALENCE_TRANS, // Derived rules for equivalence
		EFQ, RAA,
		UNIVERSAL_I, UNIVERSAL_E,
		EXISTENTIAL_I, EXISTENTIAL_E,
		EQUALITY_I, EQUALITY_E,
		EQUALITY_SYMM, EQUALITY_TRANS // Derived rules for equality
	} const rule;
	
	// Conclusion
	Node* a;

	// Auxiliary data (not going to put "nontrivial" data types into a union...)
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
		/* Distinction is made between ASSUMPTION and THEOREM in order to handle metavariable specialization within a proof.
		* The metavariable specialization rule: if a metavariable has arity K, replacing it by some ψ (resp. t) involves:
		  1. Changing bound variables in ψ to avoid naming clashes in Step 3.
		  2. Assigning new indices "unused across the whole derivation" to free variables with indices > K in ψ.
		  3. Substituting the free variables with indices 1..K in ψ for the child terms (the terms "in the parentheses").
		* It can be proven if all metavariables inside a derivation are simultaneously specialized "consistently" (i.e.
		  the new indices given in Step 2 are the same), the derivation remains syntactically valid.
		* So Γ ⊢ φ by derivation D gives Γ_sub(D, ψ) ⊢ Γ_sub(D, ψ).
		* We may further "relax" the constraints in Step 2, by choosing indices "unused in all uncancelled hypotheses and
		  the conclusion", since the variables mentioned in the derivation which do not present in hypotheses or conclusion
		  can be renamed freely.
		* (It is easier to see that the rule is indeed semantically valid: we are just "restricting" arbitrary predicates /
		  functions to a specific subset of predicates / functions!)
		* Now note that the use of axiom schemata or previously-derived theorem schemata do not contribute to "uncancelled
		  hypotheses" - their derivation rely on no hypothesis, and in principle we may chain these derivations together
		  and do metavariable specialization on "the whole thing". (By definition, axiom schemata can be specialized freely.
		  Here we do not explicitly specialize them, just to make checking faster.)
		* (We may "relax" the constraints even further, by allowing overlap between those "extra free variables" in Step 2
		  and the "already-present free variables" in the original schema. I haven't made a syntactic proof yet, but
		  semantically it just imposes the same "variable equality" restrictions on all the hypotheses and the conclusion,
		  under which the entailment relation should remain valid. However, since this is not so intuitive and may cause
		  inconvienience, I am not allowing it at least for now.)
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

		}
		case FUNCTION_S: {

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
			// from q (except p), conclusion is q, cancelling hypothesis p from the derivation of q
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
			AXIOM_D, // Declaration of an axiom (schema)
			AXIOM_U, // Removal of an axiom (schema)
			PREDICATE_D, FUNCTION_D, // Extension by definitions (using "shorthands")
			FUNCTION_DD, // Extension by definitions (using "definite descriptions")
			FUNCTION_ID, // Extension by definitions (using "indefinite descriptions")
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
