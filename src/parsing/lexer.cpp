#include "lexer.hpp"
#include <algorithm>
#include <unordered_map>

namespace apimu::parsing {
#include "macros_open.hpp"

  // Expands `s` to ε-closure.
  // Pre: the indices where `v[]` is true must match the elements of `s`.
  auto closure(NFA const& nfa, std::vector<bool>& v, std::vector<size_t>& s) -> void {
    auto stk = s;
    while (!stk.empty()) {
      auto const x = stk.back();
      stk.pop_back();
      for (auto const& [c, u]: nfa.table[x].outs)
        if (c == 0 && !v[u]) {
          s.push_back(u);
          stk.push_back(u);
          v[u] = true;
        }
    }
  }

  auto NFA::match(IStream<Char>& stream) const -> std::optional<Symbol> {
    auto last = stream.position();
    auto res = std::optional<Symbol>();
    auto s = std::vector<size_t>();
    auto v = std::vector<bool>(table.size(), false);
    // Initial states.
    s.push_back(initial);
    v[initial] = true;
    closure(*this, v, s);
    // Match greedily, until there are no further possibilities.
    while (auto const opt = stream.advance()) {
      auto const c = *opt;
      // Reset all bits of `v[]`.
      for (auto const x: s)
        v[x] = false;
      // Move one step.
      auto t = std::vector<size_t>();
      for (auto const x: s)
        for (auto const& [d, u]: table[x].outs)
          if (d == c && !v[u]) {
            t.push_back(u);
            v[u] = true;
          }
      closure(*this, v, t);
      s.swap(t);
      // Update result if reaches accepting state.
      // Patterns with larger IDs have higher priority.
      auto curr = std::optional<Symbol>();
      for (auto const x: s)
        curr = std::max(curr, table[x].mark);
      if (curr) {
        last = stream.position();
        res = *curr;
      }
    }
    // Restore last valid position and return.
    stream.revert(last);
    return res;
  }

  auto DFA::match(IStream<Char>& stream) const -> std::optional<Symbol> {
    auto last = stream.position();
    auto res = std::optional<Symbol>();
    auto s = initial;
    // Match greedily, until there are no further possibilities.
    while (auto const opt = stream.advance()) {
      auto const c = *opt;
      if (!table[s].outs[c])
        break;
      s = *table[s].outs[c];
      // Update longest match, if applicable.
      if (auto const curr = table[s].mark) {
        last = stream.position();
        res = *curr;
      }
    }
    // Restore last valid position and return.
    stream.revert(last);
    return res;
  }

  // See: https://en.wikipedia.org/wiki/UTF-8#Encoding
  constexpr auto CharMultiMin = Char{128};

  auto AutomatonBuilder::empty() -> Subgraph {
    auto const s = _node(), t = _node();
    _transition(s, 0, t);
    return {s, t};
  }
  auto AutomatonBuilder::any() -> Subgraph {
    return range(1, CharMax);
  }
  auto AutomatonBuilder::utf8segment() -> Subgraph {
    return range(CharMultiMin, CharMax);
  }
  auto AutomatonBuilder::chars(std::vector<Char> const& ls) -> Subgraph {
    auto const s = _node(), t = _node();
    for (auto const c: ls)
      _transition(s, c, t);
    return {s, t};
  }
  auto AutomatonBuilder::except(std::vector<Char> const& ls) -> Subgraph {
    auto f = std::array<bool, CharMax + 1>{};
    for (auto const c: ls)
      f[c] = true;
    auto const s = _node(), t = _node();
    for (auto i = 1uz; i <= CharMax; i++)
      if (!f[i])
        _transition(s, static_cast<Char>(i), t);
    return {s, t};
  }
  auto AutomatonBuilder::range(Char a, Char b) -> Subgraph {
    auto const s = _node(), t = _node();
    for (auto i = size_t{a}; i <= b; i++)
      _transition(s, static_cast<Char>(i), t);
    return {s, t};
  }
  auto AutomatonBuilder::rangeExcept(Char a, Char b, std::vector<Char> const& ls) -> Subgraph {
    auto f = std::array<bool, CharMax + 1>{};
    for (auto const c: ls)
      f[c] = true;
    auto const s = _node(), t = _node();
    for (auto i = size_t{a}; i <= b; i++)
      if (!f[i])
        _transition(s, static_cast<Char>(i), t);
    return {s, t};
  }
  auto AutomatonBuilder::word(std::vector<Char> const& word) -> Subgraph {
    auto const s = _node();
    auto t = s;
    for (auto const c: word) {
      auto const curr = _node();
      _transition(t, c, curr);
      t = curr;
    }
    return {s, t};
  }
  auto AutomatonBuilder::alt(std::vector<Subgraph> const& ls) -> Subgraph {
    auto const s = _node(), t = _node();
    for (auto const& a: ls) {
      _transition(s, 0, a.first);
      _transition(a.second, 0, t);
    }
    return {s, t};
  }
  auto AutomatonBuilder::concat(std::vector<Subgraph> const& ls) -> Subgraph {
    assert(!ls.empty());
    for (auto i = 0uz; i + 1 < ls.size(); i++) {
      auto const a = ls[i], b = ls[i + 1];
      for (auto const& [c, t]: _table[b.first].outs)
        _transition(a.second, c, t);
    }
    return {ls.front().first, ls.back().second};
  }
  auto AutomatonBuilder::opt(Subgraph a) -> Subgraph {
    _transition(a.first, 0, a.second);
    return {a.first, a.second};
  }
  auto AutomatonBuilder::star(Subgraph a) -> Subgraph {
    auto const s = _node(), t = _node();
    _transition(s, 0, a.first);
    _transition(a.second, 0, t);
    _transition(a.second, 0, a.first);
    _transition(s, 0, t);
    return {s, t};
  }
  auto AutomatonBuilder::plus(Subgraph a) -> Subgraph {
    return concat({a, star(a)});
  }
  auto AutomatonBuilder::pattern(Symbol sym, Subgraph a) -> AutomatonBuilder& {
    _transition(_initial, 0, a.first);
    _table[a.second].mark = sym;
    return *this;
  }

  // Allocates a node and returns its ID.
  auto AutomatonBuilder::_node() -> size_t {
    auto const res = _table.size();
    _table.emplace_back();
    return res;
  }

  // Adds a transition from node `s` to node `t` with character `c`.
  auto AutomatonBuilder::_transition(size_t s, Char c, size_t t) -> void {
    _table[s].outs.emplace_back(c, t);
  }

  // The powerset construction algorithm.
  // See: https://en.wikipedia.org/wiki/Powerset_construction
  class PowersetConstruction {
  public:
    NFA const& nfa;
    DFA& dfa;
    std::vector<bool> v;
    std::unordered_map<std::vector<bool>, size_t> map;

    PowersetConstruction(NFA const& nfa, DFA& dfa):
        nfa(nfa),
        dfa(dfa) {}

    // Allocates a node on DFA and returns its ID. Also updates `map`.
    auto node(std::vector<bool> const& key) -> size_t {
      auto const res = dfa.table.size();
      dfa.table.emplace_back();
      return map[key] = res;
    }

    // Adds a transition from node `s` to node `t` with character `c` on DFA.
    auto transition(size_t s, Char c, size_t t) -> void {
      dfa.table[s].outs[c] = t;
    }

    // Pre: all bits of `v[]` are cleared.
    auto dfs(size_t dx, std::vector<size_t> const& s) -> void {
      // Check if `s` contains accepting states.
      // Patterns with larger IDs have higher priority.
      auto curr = std::optional<Symbol>();
      for (auto const x: s)
        curr = std::max(curr, nfa.table[x].mark);
      dfa.table[dx].mark = curr;
      // Compute transitions.
      // Invariant: all elements of `v` are false at the end of the loop.
      for (auto i = 1uz; i <= CharMax; i++) {
        auto const c = static_cast<Char>(i);
        // Compute new state.
        auto t = std::vector<size_t>();
        for (auto const x: s)
          for (auto const& [d, u]: nfa.table[x].outs)
            if (d == c && !v[u]) {
              t.push_back(u);
              v[u] = true;
            }
        if (t.empty())
          continue; // No need to clear `v`: `t` is empty.
        closure(nfa, v, t);
        // Look at the new state:
        auto const it = map.find(v);
        if (it != map.end()) {
          // Already seen.
          transition(dx, c, it->second);
          for (auto const x: t)
            v[x] = false; // Clears all bits of `v`.
        } else {
          // Have not seen before, create new DFA node and recurse.
          auto const du = node(v);
          transition(dx, c, du);
          for (auto const x: t)
            v[x] = false; // Clears all bits of `v`.
          dfs(du, t);
        }
      }
    }

    // Main function.
    auto operator()() -> void {
      auto s = std::vector<size_t>();
      v.clear();
      v.resize(nfa.table.size());
      map.clear();
      // Initial states.
      s.push_back(nfa.initial);
      v[nfa.initial] = true;
      closure(nfa, v, s);
      dfa.initial = node(v);
      for (auto const x: s)
        v[x] = false; // Clears all bits of v.
      dfs(dfa.initial, s);
    }
  };

  // The Hopcroft's state minimisation algorithm.
  // - See: https://en.wikipedia.org/wiki/DFA_minimization#Hopcroft's_algorithm
  // - See: https://en.wikipedia.org/wiki/Partition_refinement
  class PartitionRefinement {
  public:
    struct List {
      List* l;
      List* r;
      size_t x;
    };
    struct Info {
      size_t cid;
      List* ptr;
    };
    struct Class {
      size_t size;
      List* head;
      bool inDists;
    };

    Allocator<List> pool;
    DFA& dfa;

    // Ephemeral states.
    std::vector<std::vector<std::pair<size_t, size_t>>> rev; // Reverse edges.
    std::vector<Info> info;                                  // Identities (class index, pointer to list).
    std::vector<Class> cls;                                  // Classes (size, head, is used as distinguisher).
    std::vector<size_t> dists;                               // Indices of classes used as distinguisher sets.
    std::array<std::vector<size_t>, CharMax + 1> srcs;       // Character -> source set.
    std::vector<std::vector<size_t>> intersection;           // Class index -> list of intersecting states.

    explicit PartitionRefinement(DFA& dfa):
        dfa(dfa) {}

    // Adds DFA node `x` to class `i`, overwriting `info[x]`.
    auto add(size_t x, size_t i) -> void {
      cls[i].size++;
      auto const l = cls[i].head, r = l->r;
      auto const curr = pool.make(List{l, r, x});
      l->r = r->l = curr;
      info[x] = {i, curr};
    }

    // Removes DFA node `x` from its class, as indicated in `info[x]`.
    auto remove(size_t x) -> void {
      auto const [i, curr] = info[x];
      auto const l = curr->l, r = curr->r;
      l->r = r;
      r->l = l;
      cls[i].size--;
    }

    // Allocates new class and returns its ID (always equal to `partition.size() - 1`, just for convenience).
    auto newClass() -> size_t {
      auto const head = pool.make(List{nullptr, nullptr, 0uz});
      head->l = head->r = head;
      auto const index = cls.size();
      cls.push_back(Class{0uz, head, false});
      return index;
    }

    // Returns (mark -> class ID, number of classes) for the initial partition.
    // One class for each mark, plus one class (Class 0) for nodes that are not marked as accepting states.
    auto initialPartition() -> std::pair<std::unordered_map<Symbol, size_t>, size_t> {
      auto res = std::unordered_map<Symbol, size_t>();
      auto cnt = 1uz; // 0 is reserved for nodes that are not marked as accepting states.
      for (auto const& entry: dfa.table)
        if (entry.mark && !res.contains(*entry.mark))
          res[*entry.mark] = cnt++;
      return {res, cnt};
    }

    // Main function.
    auto operator()() -> void {
      auto& table = dfa.table;
      auto& initial = dfa.initial;

      // Add the dead state.
      auto const dead = table.size();
      table.emplace_back();
      auto const n = table.size();
      // Add transitions to dead state. The dead state will have all its out edges pointing to itself.
      for (auto i = 0uz; i < n; i++)
        for (auto c = 1uz; c <= CharMax; c++)
          if (!table[i].outs[c])
            table[i].outs[c] = dead;
      // Mid: all elements of `table[i].outs[c]` (for c >= 1) are nonempty.

      // Reverse edges.
      rev.clear();
      rev.resize(n);
      for (auto i = 0uz; i < n; i++)
        for (auto c = 1uz; c <= CharMax; c++)
          rev[*table[i].outs[c]].emplace_back(c, i);

      // Initial partition.
      auto const& [map, k] = initialPartition();
      cls.clear();
      for (auto i = 0uz; i < k; i++)
        newClass();
      info.clear();
      info.resize(n);
      for (auto i = 0uz; i < n; i++) {
        if (table[i].mark)
          add(i, map.at(*table[i].mark));
        else
          add(i, 0uz);
      }

      // All initial classes except Class 0 (just not needed) are used as candidate distinguisher sets.
      dists.clear();
      for (auto i = 1uz; i < k; i++) {
        dists.push_back(i);
        cls[i].inDists = true;
      }

      // Partition refinement.
      intersection.clear();
      while (!dists.empty()) {
        auto const curr = dists.back();
        dists.pop_back();
        cls[curr].inDists = false;

        // Calculate the source sets for all `c`s.
        for (auto c = 1uz; c <= CharMax; c++)
          srcs[c].clear();

        // "Examine transitions" - this occurs a limited number of times, see the long comment.
        // Note that the total size of `srcs[]` equals to this number.
        for (auto p = cls[curr].head->r; p != cls[curr].head; p = p->r)
          for (auto const& [c, src]: rev[p->x])
            srcs[c].push_back(src);

        for (auto c = 1uz; c <= CharMax; c++) {
          // Inner loop time complexity should be O(size of `srcs[c]`).
          // Mid: all elements of `intersection[]` are empty.
          intersection.resize(cls.size());
          for (auto const x: srcs[c])
            intersection[info[x].cid].push_back(x);

          // Now the total size of elements of `intersection[]` equals to the size of `srcs[c]`.
          for (auto const x: srcs[c]) {
            auto const i = info[x].cid;

            // If intersection is empty or has been processed before...
            if (i >= intersection.size() || intersection[i].empty())
              continue;
            // If difference is empty...
            if (intersection[i].size() == cls[i].size) {
              // Avoid processing multiple times, also does the clearing.
              intersection[i].clear();
              continue;
            }

            // Create a new class for the "intersection".
            auto const j = newClass();
            // Add elements into it...
            for (auto const y: intersection[i]) {
              remove(y);
              add(y, j);
            }
            // The original class (with ID = `i`) now becomes the set difference!
            // Avoid processing multiple times, also does the clearing.
            intersection[i].clear();

            // See which splits will be used as distinguisher sets.
            if (cls[i].inDists || cls[j].size <= cls[i].size) {
              dists.push_back(j);
              cls[j].inDists = true;
            } else { // !cls[i].inDists && cls[i].size < cls[j].size
              dists.push_back(i);
              cls[i].inDists = true;
            }
          }
          // Mid: all elements of `intersection[]` are empty.
        }
      }

      // Rebuild `table` and `initial`, removing the dead state.
      auto newTable = std::vector<DFA::Entry>(cls.size() - 1);
      auto const newDead = info[dead].cid;
      for (auto i = 0uz; i < table.size(); i++) {
        auto src = info[i].cid;
        if (src == newDead)
          continue;
        if (src > newDead)
          src--;
        for (auto c = 1uz; c <= CharMax; c++) {
          auto dst = info[*table[i].outs[c]].cid;
          if (dst == newDead)
            continue;
          if (dst > newDead)
            dst--;
          // Build transition.
          newTable[src].outs[c] = dst;
        }
        // Mark accepting state.
        // Also check that a class does not contain different marks.
        assert(!newTable[src].mark || newTable[src].mark == table[i].mark);
        newTable[src].mark = table[i].mark;
      }
      table.swap(newTable);
      // DFA should be nonempty.
      initial = info[initial].cid;
      assert(initial != newDead);
      if (initial > newDead)
        initial--;

      /*
       * ===== A hand-wavey argument for correctness =====
       * (For simplicity, consider DFA with an explicit dead state.)
       *
       * Name the variables in https://en.wikipedia.org/wiki/DFA_minimization#Hopcroft's_algorithm as follows:
       * - P: `cls[]`: current partition (set of classes).
       * - W: `dists[]`: (always a subset of P) classes that are candidates of "distinguisher sets".
       * - A: `cls[curr]`: distinguisher set being considered now.
       * - X: `srcs[c]`.
       * - Y: `cls[i]`.
       *
       * Claim:
       *     After the algorithm completes, any two states `u` and `v` are in different classes if an only if they have
       *     different behaviours (i.e. starting from `u` and `v`, following some same input string will end up on
       *     states with different marks).
       * - Different classes -> different behaviours: by induction (this is an invariant).
       * - Different behaviours -> different classes:
       *   - For any states `u`, `v` arriving at states with different marks after taking the input string `s`:
       *     - Let the list of states on respective paths be `u = u[0]`, ..., `u[n]` and `v = v[0]`, ..., `v[n]`.
       *     - By induction prove:
       *           For any `i`, some "distinguisher set" of `u[i]` and `v[i]` must have been the `A` at some point
       *           (where a "distinguisher set" of `a` and `b` is a set containing either `a` or `b`, but not both).
       *       - Base case (`i = n`): by assumption, states `u[n]` and `v[n]` have different marks, so they are already
       *         distinguished by some set in the initial partition.
       *         - Although this set may be splitted further before becoming an `A`, all splits remain as candidates
       *           and one of them is still a distinguisher of `u[n]` and `v[n]`.
       *       - Induction step (`i < n`): by the time the distinguisher of `u[i + 1]` and `v[i + 1]` becomes the
       *         current `A`, wlog assume `A` contains `u[i + 1]` but not `v[i + 1]`.
       *         - Then `srcs[s[i]]` contains `u[i]` but not `v[i]`.
       *         - If `u[i]` and `v[i]` are still in the same set `Y`, this implies that both `Y ∩ srcs[s[i]]` and
       *           `Y \ srcs[s[i]]` are both nonempty. So at least one of them becomes a candidate distinguisher set.
       *           Although this set may be splitted further before becoming an `A`, all splits remain as candidates
       *           and one of them is still a distinguisher of `u[i]` and `v[i]`.
       *     - Since every distinguisher set is a class, `u = u[0]` and `v = v[0]` ends up in different classes.
       *
       * ===== A hand-wavey argument for time complexity =====
       * - If a class becomes `A` (i.e. `cls[curr]`) at some point, it is removed from `W` (i.e. `dists[]`).
       *   From this point, the only other classes ever becomes `A` and overlaps with it must come from its splits.
       *   But the largest split that can possibly become `A` always has a size ≤ half of the size of current `A`.
       * - Now associate to each "examination of transition" (see comment in code above) the current `A` (`cls[curr]`).
       *   Note that the destination node `x` of that transition edge is in `A`.
       * - From this point, the largest set containing `x` that can possibly become `A` must be (or smaller than) the
       *   largest split of the current `A`, so it has size ≤ half of the size of current `A`.
       * - Since the associated `A` halves its size each time, each transition may only be examined O(log n) times.
       *
       * Number of transitions: O(|Σ|n)
       * Overall: O(|Σ|n log n)
       */
    }
  };

  auto AutomatonBuilder::makeNFA() const -> NFA {
    auto res = NFA();
    res.initial = _initial;
    res.table = _table;
    return res;
  }

  auto AutomatonBuilder::makeDFA(bool minimise) const -> DFA {
    auto nfa = makeNFA();
    auto dfa = DFA();
    auto construct = PowersetConstruction(nfa, dfa);
    construct();
    if (minimise) {
      auto refine = PartitionRefinement(dfa);
      refine();
    }
    return dfa;
  }

  // Skips the next UTF-8 code point. Returns false if no more available characters.
  // See: https://en.wikipedia.org/wiki/UTF-8#Encoding
  auto skipCodePoint(IStream<Char>& stream) -> bool {
    if (!stream.advance())
      return false;
    auto last = stream.position();
    while (auto const opt = stream.advance()) {
      auto const c = *opt;
      if ((c & 0b11000000) != 0b10000000)
        break; // NOLINT(cppcoreguidelines-avoid-magic-numbers)
      last = stream.position();
    }
    stream.revert(last);
    return true;
  }

  auto AutomatonLexer::next() -> std::optional<Token> {
    auto const orig = _stream.position();
    if (auto const opt = _automaton.match(_stream)) { // Success.
      auto const curr = _stream.position();
      return Token{opt, _stream.slice(orig, curr), orig, curr};
    } else if (skipCodePoint(_stream)) { // Failure.
      auto last = _stream.position();
      while (!_automaton.match(_stream) && skipCodePoint(_stream))
        last = _stream.position();
      _stream.revert(last);
      return Token{{}, _stream.slice(orig, last), orig, last};
    } else { // Reached EOF.
      return {};
    }
  }

#include "macros_close.hpp"
}
