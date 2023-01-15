#include "lexer.hpp"
#include <algorithm>
#include <unordered_map>

namespace Parsing {

  constexpr auto CodeUnits = Lexer::CodeUnits;

  auto cutFirstCodePoint(std::string const& s, size_t pos) -> size_t {
    if (pos >= s.size()) return 0;
    auto i = 1uz;
    for (; pos + i < s.size(); i++) {
      auto const c = static_cast<unsigned int>(s[pos + i]);
      if ((c & 0b11000000) != 0b10000000) break; // NOLINT(cppcoreguidelines-avoid-magic-numbers)
    }
    return i;
  }

  auto Lexer::nextToken() -> std::optional<Token> {
    auto skipped = std::string();
    while (!eof()) {
      auto const opt = run();
      if (opt) {
        if (!skipped.empty()) mErrors.push_back(LexerError{mPosition - skipped.size(), mPosition, skipped});
        auto const [len, id] = opt.value();
        auto const res = Token{id, mPosition, mPosition + len, mString.substr(mPosition, len)};
        mPosition += len;
        return res;
      }
      // Mid: !opt
      auto const len = cutFirstCodePoint(mString, mPosition);
      skipped += mString.substr(mPosition, len);
      mPosition += len;
    }
    // Mid: eof()
    if (!skipped.empty()) mErrors.push_back(LexerError{mPosition - skipped.size(), mPosition, skipped});
    return std::nullopt;
  }

  auto NFALexer::closure(std::vector<bool>& v, std::vector<State>& s) const -> void {
    auto stk = s;
    while (!stk.empty()) {
      auto const x = stk.back();
      stk.pop_back();
      for (auto const& [cc, u]: table[x].tr)
        if (cc == 0 && !v[u]) {
          s.push_back(u);
          stk.push_back(u);
          v[u] = true;
        }
    }
  }

  auto NFALexer::run() const -> std::optional<std::pair<size_t, size_t>> {
    auto res = std::optional<std::pair<size_t, size_t>>();
    auto s = std::vector<State>();
    auto v = std::vector<bool>(table.size(), false);
    // Initial states.
    for (auto const& initial: patterns) {
      s.push_back(initial);
      v[initial] = true;
    }
    closure(v, s);
    for (auto i = 0uz; mPosition + i < mString.size(); i++) {
      auto const c = static_cast<CodeUnit>(mString[mPosition + i]);
      // Reset v[] to all false.
      for (auto const x: s) v[x] = false;
      // Move one step.
      auto t = std::vector<State>();
      for (auto const x: s)
        for (auto const& [cc, u]: table[x].tr)
          if (cc == c && !v[u]) {
            t.push_back(u);
            v[u] = true;
          }
      closure(v, t);
      s.swap(t);
      // Update result if reaches accepting state.
      // Patterns with larger IDs have higher priority.
      auto curr = std::optional<size_t>();
      for (auto const x: s)
        if (table[x].ac)
          if (!curr || curr.value() < table[x].ac.value()) curr = table[x].ac;
      // Update longest match, if applicable.
      if (curr) res = {i + 1, curr.value()};
      // Exit if no more possible matches.
      if (s.empty()) break;
    }
    return res;
  }

  class PowersetConstruction {
  public:
    NFALexer const& nfa;
    DFALexer& dfa;
    std::vector<bool> v;
    std::unordered_map<std::vector<bool>, DFALexer::State> mp;

    PowersetConstruction(NFALexer const& nfa, DFALexer& dfa):
      nfa(nfa),
      dfa(dfa) {}

    // Allocates new node and returns its ID.
    auto node(std::vector<bool> const& key) -> size_t {
      auto const res = mp[key] = dfa.table.size();
      dfa.table.emplace_back();
      return res;
    }

    // Adds a transition from node `s` to node `t` with character C.
    auto transition(DFALexer::State s, Lexer::CodeUnit c, DFALexer::State t) -> void {
      dfa.table[s].has[c] = true;
      dfa.table[s].tr[c] = t;
    }

    // Invariant: all elements of v[] are false
    auto dfs(DFALexer::State x, std::vector<NFALexer::State> const& s) -> void {
      // Check if `s` contains accepting states.
      auto curr = std::optional<size_t>();
      for (auto const ns: s) {
        auto const opt = nfa.table[ns].ac;
        if (opt && (!curr || curr.value() < opt.value())) curr = opt;
      }
      dfa.table[x].ac = curr;
      // Compute transitions.
      // Invariant: all elements of v[] are false at the end of the loop.
      for (auto c = 1u; c < CodeUnits; c++) {
        // Compute u.
        auto t = std::vector<NFALexer::State>();
        for (auto const nx: s)
          for (auto const& [cc, nu]: nfa.table[nx].tr)
            if (cc == c && !v[nu]) {
              t.push_back(nu);
              v[nu] = true;
            }
        if (t.empty()) continue; // No need to clear v: t is empty.
        nfa.closure(v, t);
        // Look at u:
        auto const it = mp.find(v);
        if (it != mp.end()) {
          // Already seen.
          transition(x, c, it->second);
          for (auto const i: t) v[i] = false;
        } else {
          // Have not seen before, create new DFA node and recurse.
          auto const u = node(v);
          transition(x, c, u);
          for (auto const i: t) v[i] = false;
          dfs(u, t);
        }
      }
    }

    // Main function.
    auto operator()() -> void {
      auto s = std::vector<NFALexer::State>();
      v.clear();
      v.resize(nfa.table.size());
      mp.clear();
      // Initial states.
      for (auto const& initial: nfa.patterns) {
        s.push_back(initial);
        v[initial] = true;
      }
      nfa.closure(v, s);
      dfa.initial = node(v);
      for (auto const i: s) v[i] = false;
      dfs(dfa.initial, s);
    }
  };

  DFALexer::DFALexer(NFALexer const& nfa) { PowersetConstruction(nfa, *this)(); }

  // Function object for the DFA state minimisation.
  // - See: https://en.wikipedia.org/wiki/DFA_minimization#Hopcroft's_algorithm
  // - See: https://en.wikipedia.org/wiki/Partition_refinement
  // Pre: the pattern IDs in accepting states are small nonnegative integers.
  // (They are directly used as initial partition IDs.)
  class PartitionRefinement {
  public:
    using State = DFALexer::State;
    using Entry = DFALexer::Entry;

    struct List {
      List* l;
      List* r;
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

    // Ephemeral states.
    std::vector<std::vector<std::pair<Lexer::CodeUnit, State>>> rev; // Reverse edges.
    std::vector<Class> cl;                         // Classes (size, pointer to head, is used as distinguisher set).
    std::vector<Identity> id;                      // Identities (class index, pointer to list).
    std::vector<size_t> dist;                      // Indices of classes used as distinguisher sets.
    std::array<std::vector<State>, CodeUnits> dom; // Character -> domain.
    std::vector<std::vector<State>> interStates;   // Class index -> list of intersecting states.

    explicit PartitionRefinement(DFALexer& dfa):
      dfa(dfa) {}

    // Add DFA node `x` to class `i`, overwriting `id[x]`.
    auto add(State x, size_t i) -> void {
      cl[i].size++;
      auto const l = cl[i].head, r = l->r;
      auto const curr = pool.add(List{l, r, x});
      l->r = r->l = curr;
      id[x] = {i, curr};
    }

    // Remove DFA node `x` from its class, as indicated in `id[x]`.
    auto remove(State x) -> void {
      auto const [i, curr] = id[x];
      auto const l = curr->l, r = curr->r;
      l->r = r;
      r->l = l;
      cl[i].size--;
    }

    // Create new class and return its ID (always = partition.size() - 1, just for convenience).
    auto newClass() -> size_t {
      auto const head = pool.add(List{nullptr, nullptr, 0});
      head->l = head->r = head;
      auto const index = cl.size();
      cl.push_back(Class{0, head, false});
      return index;
    }

    // Main function.
    auto operator()() -> void {
      auto& table = dfa.table;
      auto& initial = dfa.initial;

      // Add the dead state.
      auto const dead = table.size();
      table.emplace_back();
      auto const n = table.size();
      auto numPatterns = 0uz;
      for (auto i = 0uz; i < n; i++) {
        if (table[i].ac) numPatterns = std::max(numPatterns, table[i].ac.value() + 1);
        // Other states now have transitions to the dead state.
        // The dead state has all its transitions pointing to itself.
        for (auto c = 1u; c < CodeUnits; c++)
          if (!table[i].has[c]) table[i].tr[c] = dead;
      }
      // `has[]` can be ignored below.

      // Process reverse edges.
      rev.clear();
      rev.resize(n);
      for (auto i = 0uz; i < n; i++) {
        for (auto c = 1u; c < CodeUnits; c++) rev[table[i].tr[c]].emplace_back(c, i);
      }

      // Initial partition (numPatterns + 1 classes).
      cl.clear();
      for (auto i = 0uz; i <= numPatterns; i++) newClass();
      id.clear();
      id.resize(n);
      for (auto i = 0uz; i < n; i++) {
        if (table[i].ac) add(i, table[i].ac.value());
        else add(i, numPatterns);
      }

      // All classes except the last one (just not needed) are used as initial distinguisher sets.
      dist.clear();
      for (auto i = 0uz; i < numPatterns; i++) {
        dist.push_back(i);
        cl[i].isDist = true;
      }

      interStates.clear();
      while (!dist.empty()) {
        auto const curr = dist.back();
        dist.pop_back();
        cl[curr].isDist = false;

        // Calculate the domain sets for all c's.
        for (auto c = 1u; c < CodeUnits; c++) dom[c].clear();
        for (auto p = cl[curr].head->r; p != cl[curr].head; p = p->r) {
          // "Examine transitions" - this occurs a limited number of times, see below.
          // Note that the total size of dom[] is bounded by this.
          for (auto const& [c, s]: rev[p->x]) dom[c].push_back(s);
        }

        for (auto c = 1u; c < CodeUnits; c++) {
          // Inner loop: time complexity should be O(size of dom[c]).
          // Mid: all entries of interStates[] are empty.
          interStates.resize(cl.size());
          for (auto const x: dom[c]) interStates[id[x].cl].push_back(x);
          for (auto const x: dom[c]) {
            auto const i = id[x].cl;

            // If intersection has been processed before...
            if (i >= interStates.size() || interStates[i].empty()) continue;
            // If difference is empty...
            if (interStates[i].size() == cl[i].size) {
              interStates[i].clear();
              continue;
            }

            // Create a new class for the "intersection".
            auto const interi = newClass();
            // Add elements into it...
            for (auto const y: interStates[i]) {
              remove(y);
              add(y, interi);
            }
            // The original class now becomes the "set difference"!
            // Avoid processing multiple times, also does the clearing.
            interStates[i].clear();

            // See which splits will be used as distinguisher sets.
            if (cl[i].isDist || cl[interi].size <= cl[i].size) {
              dist.push_back(interi);
              cl[interi].isDist = true;
            } else { // !cl[i].isDist && cl[i].size < cl[interi].size
              dist.push_back(i);
              cl[i].isDist = true;
            }
          }
          // Mid: all interStates[] are empty.
        }
      }

      // Rebuild `table` and `initial`.
      auto newTable = std::vector<Entry>(cl.size());
      auto const newInitial = id[initial].cl;
      auto const newDead = id[dead].cl;
      for (auto i = 0uz; i < table.size(); i++) {
        auto const srci = id[i].cl;
        for (auto c = 1u; c < CodeUnits; c++) {
          auto const dsti = id[table[i].tr[c]].cl;
          if (dsti != newDead) {
            newTable[srci].has[c] = true;
            newTable[srci].tr[c] = dsti;
          }
        }
        if (table[i].ac) newTable[srci].ac = table[i].ac;
      }
      table.swap(newTable);
      initial = newInitial;

      // Remove the dead state.
      for (auto i = 0uz; i + 1 < table.size(); i++) {
        if (i >= newDead) table[i] = table[i + 1];
        for (auto c = 1u; c < CodeUnits; c++) {
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

  auto DFALexer::minimise() -> void { PartitionRefinement (*this)(); }

  auto DFALexer::run() const -> std::optional<std::pair<size_t, size_t>> {
    auto res = std::optional<std::pair<size_t, size_t>>();
    auto s = initial;
    for (auto i = 0uz; mPosition + i < mString.size(); i++) {
      auto const c = static_cast<CodeUnit>(mString[mPosition + i]);
      if (!table[s].has[c]) break;
      s = table[s].tr[c];
      // Update result if reaches accepting state.
      auto const curr = table[s].ac;
      if (curr) res = {i + 1, curr.value()};
    }
    return res;
  }

}
