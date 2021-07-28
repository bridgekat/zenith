// MuTrees verification kernel
#include <iostream>
#include <stdio.h>
#include <initializer_list>
#include <vector>
#include <set>
#include <algorithm>
#include <string>
#include <sstream>
using namespace std;

/*
template <typename T>
inline void set_union_inplace(vector<T>& dst, const vector<T>& rhs) {
	vector<T> t = dst;
	dst.resize(t.size() + rhs.size());
	size_t len = std::set_union(t.begin(), t.end(), rhs.begin(), rhs.end(), dst.begin()) - dst.begin();
	dst.resize(len);
}
*/

// "We use the languages introduced below to describe structures, or **classes of structures of a given signature.**"

// *Over-encapsulation intensifies*
class Signature {
private:
	vector<unsigned int> fa, pa; // Arities
	vector<string> fs, ps, cs; // Symbols

public:
	size_t addFunction(unsigned int arity, string symbol) {
		fa.push_back(arity);
		fs.push_back(symbol);
		return fs.size() - 1u;
	}

	size_t addPredicate(unsigned int arity, string symbol) {
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
};

// Union-like classes: https://en.cppreference.com/w/cpp/language/union
class Node {
public:
	// Alphabet for a first-order language
	enum Symbol: unsigned int {
		CONSTANT = 1, VARIABLE, FUNCTION, PREDICATE,
		ABSURDITY, NEGATION, CONJUNCTION, DISJUNCTION, IMPLICATION, EQUIVALENCE,
		UNIVERSAL, EXISTENTIAL
	} const symbol;
	
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
	Node(Symbol sym): symbol(sym), s(nullptr) {
		switch (sym) {
		case CONSTANT: constant.id = 0; break;
		case VARIABLE: variable.id = 0; break;
		case FUNCTION: function.id = 0; function.c = nullptr; break;
		case PREDICATE: predicate.id = 0; predicate.c = nullptr; break;
		case ABSURDITY: case NEGATION: case CONJUNCTION: case DISJUNCTION: case IMPLICATION: case EQUIVALENCE: connective.l = connective.r = nullptr; break;
		case UNIVERSAL: case EXISTENTIAL: quantifier.l = 0; quantifier.r = nullptr; break;
		}
	};
//	Node(const Node& rhs) = default; // Implicitly-defined copy constructor copies all non-static members: https://en.cppreference.com/w/cpp/language/copy_constructor
//	Node(Node&&) = default; // Implicitly-defined move constructor moves all non-static members: https://en.cppreference.com/w/cpp/language/move_constructor
//	Node& operator= (const Node&) = default; // Implicitly-defined copy assignment operator copies all non-static members: https://en.cppreference.com/w/cpp/language/copy_assignment
//	Node& operator= (Node&&) = default; // Implicitly-defined move assignment operator moves all non-static members: https://en.cppreference.com/w/cpp/language/move_assignment
//	~Node() = default; // Implicitly-defined destructor does nothing: https://en.cppreference.com/w/cpp/language/destructor
	
	// Arity "de facto"
	unsigned int arity() const {
		if (symbol != FUNCTION && symbol != PREDICATE) return 0;
		unsigned int res = 0;
		const Node* p = (symbol == FUNCTION? function.c : predicate.c);
		while (p) p = p->s, res++;
		return res;
	}

	// Each node may only be attached to **one** parent node at a time!
	void attachChildren(const std::initializer_list<Node*>& nodes) {
		if (symbol != FUNCTION && symbol != PREDICATE) return;
		Node* last = nullptr;
		for (Node* node: nodes) {
			if (last) last->s = node;
			else (symbol == FUNCTION? function.c : predicate.c) = node;
			last = node;
		}
	}

	// Deep copy
	Node* treeClone(vector<Node>& pool) const {
		pool.emplace_back(*this);
		Node* res = &pool.back();
		switch (symbol) {
		case CONSTANT: case VARIABLE:
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
	
	// Debug output
	// Displays "[ERROR]" if not a term / formula
	string toString(const Signature& sig) const {
		switch (symbol) {
		case CONSTANT:
			return sig.constantSymbol(constant.id);
		case VARIABLE: {
			std::stringstream ss;
			ss << "x" << variable.id;
			return ss.str();
			}
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
		case ABSURDITY:
			return "⊥";
		case NEGATION:
			if (!connective.l) break;
			return "(¬" + connective.l->toString(sig) + ")";
		case CONJUNCTION:
			if (!connective.l || !connective.r) break;
			return "(" + connective.l->toString(sig) + " ∧ " + connective.r->toString(sig) + ")";
		case DISJUNCTION:
			if (!connective.l || !connective.r) break;
			return "(" + connective.l->toString(sig) + " ∨ " + connective.r->toString(sig) + ")";
		case IMPLICATION:
			if (!connective.l || !connective.r) break;
			return "(" + connective.l->toString(sig) + " → " + connective.r->toString(sig) + ")";
		case EQUIVALENCE:
			if (!connective.l || !connective.r) break;
			return "(" + connective.l->toString(sig) + " ↔ " + connective.r->toString(sig) + ")";
		case UNIVERSAL: {
			if (!quantifier.r) break;
			std::stringstream ss;
			ss << "x" << quantifier.l;
			return "(∀" + ss.str() + ": " + quantifier.r->toString(sig) + ")";
			}
		case EXISTENTIAL: {
			if (!quantifier.r) break;
			std::stringstream ss;
			ss << "x" << quantifier.l;
			return "(∃" + ss.str() + ": " + quantifier.r->toString(sig) + ")";
			}
		}
		return "[ERROR]";
	}

	// Definition 2.3.1
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
	
	// Definition 2.3.2
	// O(size)
	bool isForm(const Signature& sig) const {
		if (symbol == ABSURDITY) return true;
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
		if (symbol == NEGATION && (connective.l && connective.l->isForm(sig))) return true;
		if ((symbol == CONJUNCTION || symbol == DISJUNCTION || symbol == IMPLICATION || symbol == EQUIVALENCE)
			&& (connective.l && connective.l->isForm(sig)) && (connective.r && connective.r->isForm(sig))) return true;
		if ((symbol == UNIVERSAL || symbol == EXISTENTIAL) && (quantifier.r && quantifier.r->isForm(sig))) return true;
		return false;
	}
	
	// Internal
	void FV(set<unsigned int>& res, set<unsigned int>& upperbv) const {
		switch (symbol) {
		case CONSTANT:
			break;
		case VARIABLE:
			if (upperbv.find(variable.id) == upperbv.end()) res.insert(variable.id); // Insert if not bound
			break;
		case FUNCTION: case PREDICATE: {
			const Node* p = (symbol == FUNCTION? function.c : predicate.c);
			while (p) {
				p->FV(res, upperbv);
				p = p->s;
			}
			}
			break;
		case ABSURDITY:
			break;
		case NEGATION:
			if (connective.l) connective.l->FV(res, upperbv);
			break;
		case CONJUNCTION: case DISJUNCTION: case IMPLICATION: case EQUIVALENCE:
			if (connective.l) connective.l->FV(res, upperbv);
			if (connective.r) connective.r->FV(res, upperbv);
			break;
		case UNIVERSAL: case EXISTENTIAL:
			bool modified = upperbv.insert(quantifier.l).second;
			if (quantifier.r) quantifier.r->FV(res, upperbv);
			if (modified) upperbv.erase(quantifier.l);
			break;
		}
	}
	
	// Definition 2.3.6, 2.3.7 equivalence
	// O(size * log(# of vars))
	set<unsigned int> FV() const {
		set<unsigned int> res, upperbv;
		FV(res, upperbv);
		return res;
	}

	// Internal
	void BV(set<unsigned int>& res) const {
		switch (symbol) {
		case CONSTANT: case VARIABLE:
			break;
		case FUNCTION: case PREDICATE: {
			const Node* p = (symbol == FUNCTION? function.c : predicate.c);
			while (p) {
				p->BV(res);
				p = p->s;
			}
			}
			break;
		case ABSURDITY:
			break;
		case NEGATION:
			if (connective.l) connective.l->BV(res);
			break;
		case CONJUNCTION: case DISJUNCTION: case IMPLICATION: case EQUIVALENCE:
			if (connective.l) connective.l->BV(res);
			if (connective.r) connective.r->BV(res);
			break;
		case UNIVERSAL: case EXISTENTIAL:
			res.insert(quantifier.l);
			if (quantifier.r) quantifier.r->BV(res);
			break;
		}
	}
	
	// Definition 2.3.6, 2.3.7 equivalence
	// O(size * log(# of vars))
	set<unsigned int> BV() const {
		set<unsigned int> res;
		BV(res);
		return res;
	}
	
	// Definitions 2.3.8
	bool isClosed() { return FV().empty(); }
	bool isClosedTerm(const Signature& sig) { return isTerm(sig) && FV().empty(); } // TERM_c
	bool isSentence(const Signature& sig) { return isForm(sig) && FV().empty(); } // SENT (LR_c)
	bool isOpen() { return BV().empty(); }
	
	// Definition 2.3.9, 2.3.10: s[t/xi] or φ[t/xi] (in place)
	// O(size)
	Node* replaceVariable(unsigned int i, const Node* t, vector<Node>& pool) {
		switch (symbol) {
		case CONSTANT:
			break;
		case VARIABLE:
			if (variable.id == i) return t->treeClone(pool);
			break;
		case FUNCTION: case PREDICATE: {
			Node* p = (symbol == FUNCTION? function.c : predicate.c);
			Node** last = (symbol == FUNCTION? &function.c : &predicate.c);
			while (p) {
				// *p: next node to be processed
				// *last: the pointer that should be set to point to the new node
				Node* curr = p->replaceVariable(i, t, pool); // replaceVariable() does not affect `p->s`
				*last = curr; // Does not affect `p->s`
				last = &(curr->s); // Does not affect `p->s`
				p = p->s;
			}
			}
			break;
		case ABSURDITY:
			break;
		case NEGATION:
			if (connective.l) connective.l = connective.l->replaceVariable(i, t, pool);
			break;
		case CONJUNCTION: case DISJUNCTION: case IMPLICATION: case EQUIVALENCE:
			if (connective.l) connective.l = connective.l->replaceVariable(i, t, pool);
			if (connective.r) connective.r = connective.r->replaceVariable(i, t, pool);
			break;
		case UNIVERSAL: case EXISTENTIAL:
			if (quantifier.l != i) {
				if (quantifier.r) quantifier.r = quantifier.r->replaceVariable(i, t, pool);
			} // else: Do nothing
			break;
		}
		return this;
	}
	
	// Definition 2.3.11: φ[ψ/$i] (in place)
	// O(size)
	Node* replaceProposition(unsigned int i, const Node* psi, vector<Node>& pool) {
		switch (symbol) {
		case CONSTANT: case VARIABLE: case FUNCTION:
			break;
		case PREDICATE:
			if (predicate.id == i) return psi->treeClone(pool);
			break;
		case ABSURDITY:
			break;
		case NEGATION:
			if (connective.l) connective.l = connective.l->replaceProposition(i, psi, pool);
			break;
		case CONJUNCTION: case DISJUNCTION: case IMPLICATION: case EQUIVALENCE:
			if (connective.l) connective.l = connective.l->replaceProposition(i, psi, pool);
			if (connective.r) connective.r = connective.r->replaceProposition(i, psi, pool);
			break;
		case UNIVERSAL: case EXISTENTIAL:
			if (quantifier.r) quantifier.r = quantifier.r->replaceProposition(i, psi, pool);
			break;
		}
		return this;
	}
	
	// TODO: simultaneous substitutions

	// Definition 2.3.12, Lemma 2.3.13: t is free for xi in (*this)
	// Returns: <current result, replacement occured in tree>
	// O(size * log(# of FV(t)))
	pair<bool, bool> variableIsFreeFor(const set<unsigned int>& fvt, unsigned int i) const {
		switch (symbol) {
		case CONSTANT: break;
		case VARIABLE: return make_pair(true, variable.id == i);
		case FUNCTION: case PREDICATE: {
			bool replacement = false;
			const Node* p = (symbol == FUNCTION? function.c : predicate.c);
			while (p) {
				if (p->variableIsFreeFor(fvt, i).second) replacement = true;
				p = p->s;
			}
			return make_pair(true, replacement);
			}
		case ABSURDITY: break;
		case NEGATION:
			if (!connective.l) break;
			return connective.l->variableIsFreeFor(fvt, i);
		case CONJUNCTION: case DISJUNCTION: case IMPLICATION: case EQUIVALENCE: {
			if (!connective.l || !connective.r) break;
			pair<bool, bool> lres = connective.l->variableIsFreeFor(fvt, i);
			pair<bool, bool> rres = connective.r->variableIsFreeFor(fvt, i);
			return make_pair(lres.first && rres.first, lres.second || rres.second);
			}
		case UNIVERSAL: case EXISTENTIAL: {
			if (!quantifier.r || quantifier.l == i) break; // No replacement occurs in tree
			pair<bool, bool> rres = quantifier.r->variableIsFreeFor(fvt, i);
			bool res = ((!rres.second || fvt.find(quantifier.l) == fvt.end()) && rres.first);
			bool replacement = rres.second;
			return make_pair(res, replacement);
			}
		}
		return make_pair(true, false); // When no replacement occurs in tree
	}
	bool variableIsFreeFor(const Node* t, unsigned int i) const { return variableIsFreeFor(t->FV(), i).first; }
	
	// Definition 2.3.14, Lemma 2.3.15: ψ is free for $i in (*this)
	// Returns: <current result, replacement occured in tree>
	// O(size * log(# of FV(ψ)))
	pair<bool, bool> propositionIsFreeFor(const set<unsigned int>& fvpsi, unsigned int i) const {
		switch (symbol) {
		case CONSTANT: case VARIABLE: case FUNCTION: break;
		case PREDICATE: return make_pair(true, predicate.id == i);
		case ABSURDITY: break;
		case NEGATION:
			if (!connective.l) break;
			return connective.l->propositionIsFreeFor(fvpsi, i);
		case CONJUNCTION: case DISJUNCTION: case IMPLICATION: case EQUIVALENCE: {
			if (!connective.l || !connective.r) break;
			pair<bool, bool> lres = connective.l->propositionIsFreeFor(fvpsi, i);
			pair<bool, bool> rres = connective.r->propositionIsFreeFor(fvpsi, i);
			return make_pair(lres.first && rres.first, lres.second || rres.second);
			}
		case UNIVERSAL: case EXISTENTIAL: {
			if (!quantifier.r || quantifier.l == i) break; // No replacement occurs in tree
			pair<bool, bool> rres = quantifier.r->propositionIsFreeFor(fvpsi, i);
			bool res = ((!rres.second || fvpsi.find(quantifier.l) == fvpsi.end()) && rres.first);
			bool replacement = rres.second;
			return make_pair(res, replacement);
			}
		}
		return make_pair(true, false); // When no replacement occurs in tree
	}
	bool propositionIsFreeFor(const Node* psi, unsigned int i) const { return propositionIsFreeFor(psi->FV(), i).first; }
	
	// TODO: check the code on replacement & free-for
};

class Derivation {
public:
	// Natural Deduction rules for classical first-order logic
	enum Rule: unsigned int {
		CONJUNCTION_I, CONJUNCTION_E,
		DISJUNCTION_I, DISJUNCTION_E,
		IMPLICATION_I, IMPLICATION_E,
		NEGATION_I, NEGATION_E,
		EQUIVALENCE_I, EQUIVALENCE_E,
		EFQ, RAA,
		UNIVERSAL_I, UNIVERSAL_E,
		EXISTENTIAL_I, EXISTENTIAL_E
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

	// Definitions in 1.4, 1.6, 2.8 and 2.9
	// O(size)
	bool check(const set<const Node*>& hyp) {
		// #####
		return false;
	}
};


int main() {
	
	{ // Experiment 1
		Signature sig;
		const unsigned int ZERO = sig.addConstant("0");
		const unsigned int ADD = sig.addFunction(2, "+");
		const unsigned int MUL = sig.addFunction(2, "*");
		const unsigned int SUCC = sig.addFunction(1, "S");
		const unsigned int EQUAL = sig.addPredicate(2, "=");
		const unsigned int LESS = sig.addPredicate(2, "<");
		const unsigned int LEQUAL = sig.addPredicate(2, "≤");

		Node p(Node::UNIVERSAL), q(Node::UNIVERSAL);
		p.quantifier.l = 1; q.quantifier.l = 2;
		Node a(Node::EQUIVALENCE), b(Node::PREDICATE), c(Node::DISJUNCTION), d(Node::PREDICATE), e(Node::PREDICATE);
		b.predicate.id = LEQUAL; d.predicate.id = LESS; e.predicate.id = EQUAL;
		Node x0(Node::VARIABLE), y0(Node::VARIABLE), x1(Node::VARIABLE), y1(Node::VARIABLE), x2(Node::VARIABLE), y2(Node::VARIABLE), x3(Node::VARIABLE), y3(Node::VARIABLE);
		x0.variable.id = x1.variable.id = x2.variable.id = x3.variable.id = 1;
		y0.variable.id = y1.variable.id = y2.variable.id = y3.variable.id = 2;

		cout << a.isTerm(sig) << a.isForm(sig) << e.isTerm(sig) << e.isForm(sig) << endl; // 0000
		a.connective.l = &b; a.connective.r = &c;
		cout << a.isForm(sig) << b.isForm(sig) << b.isTerm(sig) << endl; // 000
		b.attachChildren({ &x1, &y1 });
		cout << a.isForm(sig) << b.isForm(sig) << b.isTerm(sig) << endl; // 010
		c.connective.l = &d; c.connective.r = &e;
		cout << a.isForm(sig) << c.isForm(sig) << endl; // 00
		d.attachChildren({ &x2, &y2 });
		cout << a.isForm(sig) << c.isForm(sig) << endl; // 00
		e.attachChildren({ &x3, &y3 });
		cout << a.isForm(sig) << c.isForm(sig) << endl; // 11

		cout << b.toString(sig) << endl; // ≤(x1, x2)
		cout << a.toString(sig) << endl; // (≤(x1, x2) ↔ (<(x1, x2) ∨ =(x1, x2)))

		p.quantifier.r = &q; q.quantifier.r = &a;
		cout << p.toString(sig) << endl; // (∀x1: (∀x2: (≤(x1, x2) ↔ (<(x1, x2) ∨ =(x1, x2)))))

		cout << a.FV().size() << a.BV().size() << endl; // 20
		cout << q.FV().size() << q.BV().size() << endl; // 11
		cout << p.FV().size() << p.BV().size() << endl; // 02
	}

	return 0;
}
