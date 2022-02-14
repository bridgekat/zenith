#include <vector>
#include <unordered_map>
#include <core/base.hpp>
#include "lexer.hpp"


namespace Parsing {

  string cutFirstCodepoint(const string& s) {
    if (s.empty()) return s;
    size_t pos = 1;
    for (; pos < s.size(); pos++) {
      unsigned char c = s[pos];
      if ((c & 0b11000000) != 0b10000000) break;
    }
    return s.substr(pos);
  }

  void NFALexer::ignoreNextCodepoint() { rest = cutFirstCodepoint(rest); }
  void DFALexer::ignoreNextCodepoint() { rest = cutFirstCodepoint(rest); }

  // Directly run NFA
  optional<pair<size_t, TokenID>> NFALexer::run(const string& str) const {
    optional<pair<size_t, TokenID>> res = nullopt;
    vector<State> s;
    vector<bool> v(table.size(), false);

    // A helper function
    // Pre: the indices where v[] is true must match the elements of s
    auto closure = [this] (vector<bool>& v, vector<State>& s) {
      // Expand to epsilon closure (using DFS)
      vector<State> stk = s;
      while (!stk.empty()) {
        State x = stk.back(); stk.pop_back();
        for (auto [cc, u]: table[x].tr) if (cc == 0 && !v[u]) {
          s.push_back(u);
          stk.push_back(u);
          v[u] = true;
        }
      }
    };

    s.push_back(initial);
    v[initial] = true;
    closure(v, s);
    for (size_t i = 0; i < str.size(); i++) {
      unsigned char c = str[i];
      // Reset v[] to false
      for (State x: s) v[x] = false;
      // Move one step
      vector<State> t;
      for (State x: s) for (auto [cc, u]: table[x].tr) if (cc == c && !v[u]) {
        t.push_back(u);
        v[u] = true;
      }
      closure(v, t);
      s.swap(t);
      // Update result if reaches accepting state
      // Patterns with smaller IDs have higher priority
      optional<TokenID> curr = nullopt;
      for (State x: s) if (table[x].ac) {
        if (!curr || curr.value() > table[x].ac.value()) curr = table[x].ac;
      }
      // Update longest match, if applicable
      if (curr) res = { i + 1, curr.value() };
      // Exit if no more possible matches
      if (s.empty()) break;
    }
    return res;
  }

  optional<Token> NFALexer::getNextToken() {
    auto opt = run(rest);
    if (!opt) return nullopt;
    auto [len, id] = opt.value();
    Token res{ id, rest.substr(0, len) };
    rest = rest.substr(len);
    return res;
  }

  using std::unordered_map;

  // Function object for the DFA construction from NFA
  class PowersetConstruction {
  public:
    const NFALexer& nfa;
    DFALexer* dfa;
    vector<bool> v;
    unordered_map<vector<bool>, DFALexer::State> mp;

    PowersetConstruction(const NFALexer& nfa, DFALexer* dfa): nfa(nfa), dfa(dfa), v(), mp() {}
    PowersetConstruction(const PowersetConstruction&) = delete;
    PowersetConstruction& operator=(const PowersetConstruction&) = delete;

    void closure(vector<bool>& v, vector<NFALexer::State>& s) const {
      // Expand to epsilon closure (using DFS)
      vector<NFALexer::State> stk = s;
      while (!stk.empty()) {
        NFALexer::State nx = stk.back(); stk.pop_back();
        for (auto [cc, nu]: nfa.table[nx].tr) if (cc == 0 && !v[nu]) {
          s.push_back(nu);
          stk.push_back(nu);
          v[nu] = true;
        }
      }
    };

    #define node(x_, s_) \
      x_ = mp[s_] = dfa->table.size(); \
      dfa->table.emplace_back()
    #define trans(s_, c_, t_) \
      dfa->table[s_].has[c_] = true; \
      dfa->table[s_].tr[c_] = t_
    #define clearv(s_) \
      for (NFALexer::State i: s_) v[i] = false;

    // Invariant: all elements of v[] are false
    void dfs(DFALexer::State x, const vector<NFALexer::State>& s) {
      // Check if `s` contains accepting states
      optional<TokenID> curr;
      for (auto ns: s) {
        auto opt = nfa.table[ns].ac;
        if (opt && (!curr || curr.value() > opt.value())) curr = opt;
      }
      dfa->table[x].ac = curr;
      // Compute transitions
      // Invariant: all elements of v[] are false at the end of the loop
      for (unsigned int c = 0x01; c <= 0xFF; c++) {
        // Compute u
        vector<NFALexer::State> t;
        for (auto nx: s) for (auto [cc, nu]: nfa.table[nx].tr) {
          if (cc == c && !v[nu]) {
            t.push_back(nu);
            v[nu] = true;
          }
        }
        if (t.empty()) continue; // No need to clear v: t is empty
        closure(v, t);
        // Look at u:
        auto it = mp.find(v);
        if (it != mp.end()) {
          // Already seen
          trans(x, c, it->second);
          clearv(t);
        } else {
          // Haven't seen before, create new DFA node and recurse
          node(DFALexer::State u, v);
          trans(x, c, u);
          clearv(t);
          dfs(u, t);
        }
      }
    }

    void operator() () {
      v.clear(); v.resize(nfa.table.size());
      mp.clear();
      vector<NFALexer::State> s = { nfa.initial };
      v[nfa.initial] = true;
      closure(v, s);
      node(dfa->initial, v);
      clearv(s);
      dfs(dfa->initial, s);
    }

    #undef node
    #undef trans
    #undef clearv
  };

  DFALexer::DFALexer(const NFALexer& nfa): table(), initial(0), rest() {
    PowersetConstruction(nfa, this)();
  }

  // Function object for the DFA state minimization
  //   See: https://en.wikipedia.org/wiki/DFA_minimization#Hopcroft's_algorithm
  //   See: https://en.wikipedia.org/wiki/Partition_refinement
  // Pre: the TokenIDs in accepting states are small nonnegative integers.
  // (They are directly used as initial partition IDs; I am too lazy so I didn't make a map.)
  class PartitionRefinement {
  public:
    typedef DFALexer::State State;
    typedef DFALexer::Entry Entry;
    struct List { List *l, *r; State x; };

    Core::Allocator<List> pool;
    DFALexer* dfa;

    struct Class { size_t size; List* head; bool isDist; };
    struct Identity { size_t cl; List* ptr; };

    // Ephemeral states (I put these here only to unclutter the main function...)
    vector<vector<pair<unsigned char, State>>> rev; // Reverse edges
    vector<Class> cl;                   // Classes (size, pointer to head, is used as distinguisher set)
    vector<Identity> id;                // Identities (class index, pointer to list)
    vector<size_t> dist;                // Indices of classes used as distinguisher sets
    vector<State> dom[0x100];           // Character -> domain
    vector<vector<State>> interStates;  // Class index -> list of intersecting states

    explicit PartitionRefinement(DFALexer* dfa):
      pool(), dfa(dfa), rev(), cl(), id(), dist(), dom(), interStates() {}
    PartitionRefinement(const PartitionRefinement&) = delete;
    PartitionRefinement& operator=(const PartitionRefinement&) = delete;

    // Add DFA node `x` to class `i`, overwriting `id[x]`
    void add(State x, size_t i) {
      cl[i].size++;
      List* l = cl[i].head, * r = l->r;
      List* curr = pool.pushBack({ l, r, x });
      l->r = r->l = curr;
      id[x] = { i, curr };
    }

    // Remove DFA node `x` from its class, as indicated in `id[x]`
    void remove(State x) {
      auto [i, curr] = id[x];
      List* l = curr->l, * r = curr->r;
      l->r = r; r->l = l;
      cl[i].size--;
    }

    // Create new class and return its ID (always = partition.size() - 1, just for convenience)
    size_t newClass() {
      List* head = pool.pushBack({ nullptr, nullptr, 0 });
      head->l = head->r = head;
      size_t index = cl.size();
      cl.emplace_back(0, head, false);
      return index;
    }

    void operator() () {
      auto& table = dfa->table;
      auto& initial = dfa->initial;

      // Add the dead state
      size_t dead = table.size();
      table.emplace_back();
      size_t n = table.size();
      TokenID numTokens = 0;
      for (size_t i = 0; i < n; i++) {
        if (table[i].ac) numTokens = std::max(numTokens, table[i].ac.value() + 1);
        // Other states now have transitions to the dead state
        // The dead state has all its transitions pointing to itself
        for (unsigned int c = 0x01; c <= 0xFF; c++) if (!table[i].has[c]) table[i].tr[c] = dead;
      }
      // `has[]` can be ignored below

      // Process reverse edges (arcs)
      rev.clear(); rev.resize(n);
      for (size_t i = 0; i < n; i++) {
        for (unsigned int c = 0x01; c <= 0xFF; c++) rev[table[i].tr[c]].emplace_back(c, i);
      }

      // Initial partition (numTokens + 1 classes)
      cl.clear();
      for (size_t i = 0; i <= numTokens; i++) newClass();
      id.clear(); id.resize(n);
      for (size_t i = 0; i < n; i++) {
        if (table[i].ac) add(i, table[i].ac.value());
        else             add(i, numTokens);
      }

      // All classes except the last one (just not needed) are used as initial distinguisher sets
      dist.clear();
      for (size_t i = 0; i < numTokens; i++) {
        dist.push_back(i);
        cl[i].isDist = true;
      }

      interStates.clear();
      while (!dist.empty()) {
        size_t curr = dist.back();
        dist.pop_back();
        cl[curr].isDist = false;

        // Calculate the domain sets for all c's
        for (unsigned int c = 0x01; c <= 0xFF; c++) dom[c].clear();
        for (const List* p = cl[curr].head->r; p != cl[curr].head; p = p->r) {
          // "Examine transitions" - this occurs a limited number of times, see below
          // Note that the total size of dom[] is bounded by this
          for (auto [c, s]: rev[p->x]) dom[c].push_back(s);
        }

        for (unsigned int c = 0x01; c <= 0xFF; c++) {
          // Inner loop: time complexity should be O(size of dom[c])
          // Pre: all entries of interStates[] are empty
          interStates.resize(cl.size());
          for (State x: dom[c]) interStates[id[x].cl].push_back(x);
          for (State x: dom[c]) {
            size_t i = id[x].cl;

            // If intersection has been processed before...
            if (i >= interStates.size() || interStates[i].empty()) continue;
            // If difference is empty...
            if (interStates[i].size() == cl[i].size) {
              interStates[i].clear();
              continue;
            }

            // Create a new class for the "intersection"
            size_t interi = newClass();
            // Add elements into it...
            for (State y: interStates[i]) {
              remove(y);
              add(y, interi);
            }
            // The original class now becomes the "set difference"!
            // Avoid processing multiple times, also does the clearing
            interStates[i].clear();

            // See which splits will be used as distinguisher sets
            if (cl[i].isDist || cl[interi].size <= cl[i].size) {
              dist.push_back(interi);
              cl[interi].isDist = true;
            } else { // (!cl[i].isDist && cl[i].size < cl[interi].size)
              dist.push_back(i);
              cl[i].isDist = true;
            }
          }
          // Post: all interStates[] are empty at this time
        }
      }

      // Rebuild `table` and `initial`
      vector<Entry> newTable(cl.size());
      State newInitial = id[initial].cl, newDead = id[dead].cl;
      for (size_t i = 0; i < table.size(); i++) {
        State srci = id[i].cl;
        for (unsigned int c = 0x01; c <= 0xFF; c++) {
          State dsti = id[table[i].tr[c]].cl;
          if (dsti != newDead) {
            newTable[srci].has[c] = true;
            newTable[srci].tr[c] = dsti;
          }
        }
        if (table[i].ac) newTable[srci].ac = table[i].ac;
      }
      table.swap(newTable);
      initial = newInitial;

      // Remove the dead state
      for (size_t i = 0; i + 1 < table.size(); i++) {
        if (i >= newDead) table[i] = table[i + 1];
        for (unsigned int c = 0x01; c <= 0xFF; c++) {
          if (table[i].has[c] && table[i].tr[c] > newDead) table[i].tr[c]--;
        }
      }
      table.pop_back();
      if (initial > newDead) initial--;

      /*
      * ===== A hand-wavey argument for correctness =====
      * Different classes -> different behaviors: by induction.
      * Different behaviors -> different classes:
      *   (Lemma: for any two disjoint classes, a "distinguisher of them" must have existed.)
      *   For any states s, t arriving at different accepting states after taking the path a:
      *     Let the intermediate states be i1 ... in and j1 ... jn.
      *     For any k, some "distinguisher of ik and jk" must have existed: by induction.
      *       Initial (k = n): in and jn are different non/accepting values so they are in different initial partitions...
      *       Step (k < k' - 1):
      *         By the time the "distinguisher of ik' and jk'" is current,
      *         either ik and jk in the same class (it then get splitted, one of the split becomes distinguisher),
      *         or they are in different classes (by Lemma).
      *     So i1 and j1 (s and t) must be in different classes
      *     (All distinguishers are classes; all classes are disjoint).
      *
      * ===== A hand-wavey argument for time complexity =====
      * (Lemma: if a class is ever used ("currented") as a distinguisher,
      *         the only overlapping distinguishers ever "currented" must come from its splits;
      *         but each split that can possibly be used as a distinguisher must ≤ half of the original size.)
      * Associate each "examination of transition" with the current distinguisher set.
      *   The destination state `dst` of the transition must be in the distinguisher set!
      *   This set then splits, any split "ever used as distinguisher" that contains `dst` must ≤ half of the original size.
      *   So each transition may only be examined O(log n) times...
      * Overall: O(|Σ|n log n)
      */

      // How could a human ever come up with such an algorithm... 这玩意是人能发明出来的吗
    }
  };

  void DFALexer::optimize() {
    PartitionRefinement(this)();
  }

  // Run DFA
  optional<pair<size_t, TokenID>> DFALexer::run(const string& str) const {
    optional<pair<size_t, TokenID>> res = nullopt;
    State s = initial;
    for (size_t i = 0; i < str.size(); i++) {
      unsigned char c = str[i];
      if (!table[s].has[c]) break;
      s = table[s].tr[c];
      // Update result if reaches accepting state
      auto curr = table[s].ac;
      if (curr) res = { i + 1, curr.value() };
    }
    return res;
  }

  optional<Token> DFALexer::getNextToken() {
    auto opt = run(rest);
    if (!opt) return nullopt;
    auto [len, id] = opt.value();
    Token res{ id, rest.substr(0, len) };
    rest = rest.substr(len);
    return res;
  }

  /*
  * It is so confusing that different "regular expression" implementations actually provide different
  * non-regular extensions and even different behaviors on basic constructs like alternation!
  * The `grep` in POSIX follows the "leftmost longest match" rule, and the same can be said for this lexer.
  * For example, if you match string `ab` with the pattern `a|ab`, you will get `ab`.
  * However, "modern" regex engines like the ones used in TextMate and VSCode use "non-greedy alternation"
  * and this behavior cannot be changed. The above pattern will match `a` only!
  * This creates a problem if we want to use a single, unified representation for lexical rules, as our
  * automata-based lexers cannot "mix" greedy and non-greedy constructs (we must use either the longest
  * match or the shortest one...)
  *
  * The following algorithm will convert our DFA representation into regexes that uses "negative lookahead"
  * to simulate "greedy alternation" -- the regex accepts only if no further matches are available.
  * See: https://macromates.com/manual/en/regular_expressions
  * See: https://courses.engr.illinois.edu/cs374/fa2017/extra_notes/01_nfa_to_reg.pdf
  */
  string DFALexer::toTextMateGrammar() const {
    // TODO (this is probably too costly and not worth the trouble...)
    throw Core::NotImplemented();
  }

}
