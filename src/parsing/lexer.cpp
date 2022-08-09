#include "lexer.hpp"
#include <algorithm>
#include <unordered_map>

namespace Parsing {

  constexpr unsigned int CodeUnits = Lexer::CodeUnits;

  size_t cutFirstCodePoint(const string& s, size_t pos) {
    if (pos >= s.size()) return 0;
    size_t i = 1;
    for (; pos + i < s.size(); i++) {
      char8_t c = s[pos + i];
      if ((c & 0b11000000) != 0b10000000) break; // NOLINT(cppcoreguidelines-avoid-magic-numbers)
    }
    return i;
  }

  optional<Token> Lexer::nextToken() {
    string skipped;
    while (!eof()) {
      auto opt = run();
      if (opt) {
        if (!skipped.empty()) errors.push_back(ErrorInfo{pos - skipped.size(), pos, skipped});
        auto [len, id] = opt.value();
        Token res{id, pos, pos + len, str.substr(pos, len)};
        pos += len;
        return res;
      }
      // Mid: !opt
      size_t len = cutFirstCodePoint(str, pos);
      skipped += str.substr(pos, len);
      pos += len;
    }
    // Mid: eof()
    if (!skipped.empty()) errors.push_back(ErrorInfo{pos - skipped.size(), pos, skipped});
    return nullopt;
  }

  // Directly run NFA
  optional<pair<size_t, size_t>> NFALexer::run() const {
    optional<pair<size_t, size_t>> res = nullopt;
    vector<State> s;
    vector<bool> v(table.size(), false);

    // A helper function
    // Pre: the indices where v[] is true must match the elements of s
    auto closure = [this](vector<bool>& v, vector<State>& s) {
      // Expand to epsilon closure (using DFS)
      vector<State> stk = s;
      while (!stk.empty()) {
        State x = stk.back();
        stk.pop_back();
        for (auto [cc, u]: table[x].tr)
          if (cc == 0 && !v[u]) {
            s.push_back(u);
            stk.push_back(u);
            v[u] = true;
          }
      }
    };

    // Initial states
    for (const auto& initial: patterns) {
      s.push_back(initial);
      v[initial] = true;
    }
    closure(v, s);
    for (size_t i = 0; pos + i < str.size(); i++) {
      char8_t c = str[pos + i];
      // Reset v[] to all false
      for (State x: s) v[x] = false;
      // Move one step
      vector<State> t;
      for (State x: s)
        for (auto [cc, u]: table[x].tr)
          if (cc == c && !v[u]) {
            t.push_back(u);
            v[u] = true;
          }
      closure(v, t);
      s.swap(t);
      // Update result if reaches accepting state
      // Patterns with larger IDs have higher priority
      optional<size_t> curr = nullopt;
      for (State x: s)
        if (table[x].ac) {
          if (!curr || curr.value() < table[x].ac.value()) curr = table[x].ac;
        }
      // Update longest match, if applicable
      if (curr) res = {i + 1, curr.value()};
      // Exit if no more possible matches
      if (s.empty()) break;
    }
    return res;
  }

  using std::unordered_map;

  // Function object for the DFA construction from NFA
  class PowersetConstruction {
  public:
    const NFALexer& nfa;
    DFALexer& dfa;
    vector<bool> v;
    unordered_map<vector<bool>, DFALexer::State> mp;

    PowersetConstruction(const NFALexer& nfa, DFALexer& dfa): nfa(nfa), dfa(dfa), v(), mp() {}

    void closure(vector<NFALexer::State>& s) {
      // Expand `s` and `v` to epsilon closure (using DFS)
      vector<NFALexer::State> stk = s;
      while (!stk.empty()) {
        NFALexer::State nx = stk.back();
        stk.pop_back();
        for (auto [cc, nu]: nfa.table[nx].tr)
          if (cc == 0 && !v[nu]) {
            s.push_back(nu);
            stk.push_back(nu);
            v[nu] = true;
          }
      }
    };

#define clearv(s_) \
  for (NFALexer::State i: s_) v[i] = false;
#define node(x_, s_)              \
  x_ = mp[s_] = dfa.table.size(); \
  dfa.table.emplace_back()
#define trans(s_, c_, t_)       \
  dfa.table[s_].has[c_] = true; \
  dfa.table[s_].tr[c_] = t_

    // Invariant: all elements of v[] are false
    void dfs(DFALexer::State x, const vector<NFALexer::State>& s) {
      // Check if `s` contains accepting states
      optional<size_t> curr;
      for (auto ns: s) {
        auto opt = nfa.table[ns].ac;
        if (opt && (!curr || curr.value() < opt.value())) curr = opt;
      }
      dfa.table[x].ac = curr;
      // Compute transitions
      // Invariant: all elements of v[] are false at the end of the loop
      for (unsigned int c = 1; c < CodeUnits; c++) {
        // Compute u
        vector<NFALexer::State> t;
        for (auto nx: s)
          for (auto [cc, nu]: nfa.table[nx].tr) {
            if (cc == c && !v[nu]) {
              t.push_back(nu);
              v[nu] = true;
            }
          }
        if (t.empty()) continue; // No need to clear v: t is empty
        closure(t);
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

    void operator()() {
      vector<NFALexer::State> s;
      v.clear();
      v.resize(nfa.table.size());
      mp.clear();
      // Initial states
      for (const auto& initial: nfa.patterns) {
        s.push_back(initial);
        v[initial] = true;
      }
      closure(s);
      node(dfa.initial, v);
      clearv(s);
      dfs(dfa.initial, s);
    }

#undef node
#undef trans
#undef clearv
  };

  DFALexer::DFALexer(const NFALexer& nfa): Lexer(), table(), initial(0) { PowersetConstruction(nfa, *this)(); }

  // Function object for the DFA state minimization
  //   See: https://en.wikipedia.org/wiki/DFA_minimization#Hopcroft's_algorithm
  //   See: https://en.wikipedia.org/wiki/Partition_refinement
  // Pre: the pattern IDs in accepting states are small nonnegative integers.
  // (They are directly used as initial partition IDs)
  class PartitionRefinement {
  public:
    using State = DFALexer::State;
    using Entry = DFALexer::Entry;
    struct List {
      List *l, *r;
      State x;
    };
    struct Class {
      size_t size;
      List* head;
      bool isDist;
    };
    struct Identity {
      size_t cl;
      List* ptr;
    };

    Core::Allocator<List> pool;
    DFALexer& dfa;

    // Ephemeral states
    vector<vector<pair<char8_t, State>>> rev; // Reverse edges
    vector<Class> cl;                         // Classes (size, pointer to head, is used as distinguisher set)
    vector<Identity> id;                      // Identities (class index, pointer to list)
    vector<size_t> dist;                      // Indices of classes used as distinguisher sets
    array<vector<State>, CodeUnits> dom;      // Character -> domain
    vector<vector<State>> interStates;        // Class index -> list of intersecting states

    explicit PartitionRefinement(DFALexer& dfa): pool(), dfa(dfa), rev(), cl(), id(), dist(), dom(), interStates() {}

    // Add DFA node `x` to class `i`, overwriting `id[x]`
    void add(State x, size_t i) {
      cl[i].size++;
      List *l = cl[i].head, *r = l->r;
      List* curr = pool.pushBack(List{l, r, x});
      l->r = r->l = curr;
      id[x] = {i, curr};
    }

    // Remove DFA node `x` from its class, as indicated in `id[x]`
    void remove(State x) {
      auto [i, curr] = id[x];
      List *l = curr->l, *r = curr->r;
      l->r = r;
      r->l = l;
      cl[i].size--;
    }

    // Create new class and return its ID (always = partition.size() - 1, just for convenience)
    size_t newClass() {
      List* head = pool.pushBack(List{nullptr, nullptr, 0});
      head->l = head->r = head;
      size_t index = cl.size();
      cl.push_back(Class{0, head, false});
      return index;
    }

    void operator()() {
      auto& table = dfa.table;
      auto& initial = dfa.initial;

      // Add the dead state
      State dead = table.size();
      table.emplace_back();
      State n = table.size();
      size_t numPatterns = 0;
      for (State i = 0; i < n; i++) {
        if (table[i].ac) numPatterns = std::max(numPatterns, table[i].ac.value() + 1);
        // Other states now have transitions to the dead state
        // The dead state has all its transitions pointing to itself
        for (unsigned int c = 1; c < CodeUnits; c++)
          if (!table[i].has[c]) table[i].tr[c] = dead;
      }
      // `has[]` can be ignored below

      // Process reverse edges (arcs)
      rev.clear();
      rev.resize(n);
      for (State i = 0; i < n; i++) {
        for (unsigned int c = 1; c < CodeUnits; c++) rev[table[i].tr[c]].emplace_back(static_cast<char8_t>(c), i);
      }

      // Initial partition (numPatterns + 1 classes)
      cl.clear();
      for (size_t i = 0; i <= numPatterns; i++) newClass();
      id.clear();
      id.resize(n);
      for (State i = 0; i < n; i++) {
        if (table[i].ac) add(i, table[i].ac.value());
        else add(i, numPatterns);
      }

      // All classes except the last one (just not needed) are used as initial distinguisher sets
      dist.clear();
      for (size_t i = 0; i < numPatterns; i++) {
        dist.push_back(i);
        cl[i].isDist = true;
      }

      interStates.clear();
      while (!dist.empty()) {
        size_t curr = dist.back();
        dist.pop_back();
        cl[curr].isDist = false;

        // Calculate the domain sets for all c's
        for (unsigned int c = 1; c < CodeUnits; c++) dom[c].clear();
        for (const List* p = cl[curr].head->r; p != cl[curr].head; p = p->r) {
          // "Examine transitions" - this occurs a limited number of times, see below
          // Note that the total size of dom[] is bounded by this
          for (auto [c, s]: rev[p->x]) dom[c].push_back(s);
        }

        for (unsigned int c = 1; c < CodeUnits; c++) {
          // Inner loop: time complexity should be O(size of dom[c])
          // Mid: all entries of interStates[] are empty
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
            } else { // Mid: !cl[i].isDist && cl[i].size < cl[interi].size
              dist.push_back(i);
              cl[i].isDist = true;
            }
          }
          // Mid: all interStates[] are empty
        }
      }

      // Rebuild `table` and `initial`
      vector<Entry> newTable(cl.size());
      State newInitial = id[initial].cl, newDead = id[dead].cl;
      for (State i = 0; i < table.size(); i++) {
        State srci = id[i].cl;
        for (unsigned int c = 1; c < CodeUnits; c++) {
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
      for (State i = 0; i + 1 < table.size(); i++) {
        if (i >= newDead) table[i] = table[i + 1];
        for (unsigned int c = 1; c < CodeUnits; c++) {
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
       *       Initial (k = n): in and jn are different non/accepting values so they are in different initial
       * partitions... Step (k < k' - 1): By the time the "distinguisher of ik' and jk'" is current, either ik and jk in
       * the same class (it then get splitted, one of the split becomes distinguisher), or they are in different classes
       * (by Lemma). So i1 and j1 (s and t) must be in different classes (All distinguishers are classes; all classes
       * are disjoint).
       *
       * ===== A hand-wavey argument for time complexity =====
       * (Lemma: if a class is ever used ("currented") as a distinguisher,
       *         the only overlapping distinguishers ever "currented" must come from its splits;
       *         but each split that can possibly be used as a distinguisher must ≤ half of the original size.)
       * Associate each "examination of transition" with the current distinguisher set.
       *   The destination state `dst` of the transition must be in the distinguisher set!
       *   This set then splits, any split "ever used as distinguisher" that contains `dst` must ≤ half of the original
       * size. So each transition may only be examined O(log n) times... Overall: O(|Σ|n log n)
       */

      // How could a human ever come up with such an algorithm... 这玩意是人能发明出来的吗
    }
  };

  void DFALexer::optimize() { PartitionRefinement (*this)(); }

  // Run DFA
  optional<pair<size_t, size_t>> DFALexer::run() const {
    optional<pair<size_t, size_t>> res = nullopt;
    State s = initial;
    for (size_t i = 0; pos + i < str.size(); i++) {
      char8_t c = str[pos + i];
      if (!table[s].has[c]) break;
      s = table[s].tr[c];
      // Update result if reaches accepting state
      auto curr = table[s].ac;
      if (curr) res = {i + 1, curr.value()};
    }
    return res;
  }

}
