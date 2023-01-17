#include "lexer.hpp"
#include <algorithm>
#include <unordered_map>

namespace Parsing {

  auto NFA::closure(std::vector<bool>& v, std::vector<size_t>& s) const -> void {
    auto stk = s;
    while (!stk.empty()) {
      auto const x = stk.back();
      stk.pop_back();
      for (auto const& [c, u]: mTable[x].outs)
        if (c == 0 && !v[u]) {
          s.push_back(u);
          stk.push_back(u);
          v[u] = true;
        }
    }
  }

  auto NFA::match(Generator<Char>& string) const -> std::optional<Symbol> {
    auto last = string.position();
    auto res = std::optional<Symbol>();
    auto s = std::vector<size_t>();
    auto v = std::vector<bool>(mTable.size(), false);
    // Initial states.
    s.push_back(mInitial);
    v[mInitial] = true;
    closure(v, s);
    // Match greedily, until there are no further possibilities.
    while (!string.eof() && !s.empty()) {
      auto const c = string.advance();
      // Reset all bits of `v[]`.
      for (auto const x: s) v[x] = false;
      // Move one step.
      auto t = std::vector<size_t>();
      for (auto const x: s)
        for (auto const& [d, u]: mTable[x].outs)
          if (d == c && !v[u]) {
            t.push_back(u);
            v[u] = true;
          }
      closure(v, t);
      s.swap(t);
      // Update result if reaches accepting state.
      // Patterns with larger IDs have higher priority.
      auto curr = std::optional<Symbol>();
      for (auto const x: s) curr = std::max(curr, mTable[x].mark);
      if (curr) {
        last = string.position();
        res = *curr;
      }
    }
    // Restore last valid position and return.
    string.revert(last);
    return res;
  }

  class PowersetConstruction {
  public:
    NFA const& nfa;
    DFA& dfa;
    std::vector<bool> v;
    std::unordered_map<std::vector<bool>, size_t> map;

    PowersetConstruction(NFA const& nfa, DFA& dfa):
      nfa(nfa),
      dfa(dfa) {}

    // Pre: all bits of `v[]` are cleared.
    auto dfs(size_t dx, std::vector<size_t> const& s) -> void {
      // Check if `s` contains accepting states.
      // Patterns with larger IDs have higher priority.
      auto curr = std::optional<Symbol>();
      for (auto const x: s) curr = std::max(curr, nfa.mTable[x].mark);
      dfa.mTable[dx].mark = curr;
      // Compute transitions.
      // Invariant: all elements of `v` are false at the end of the loop.
      for (auto c = 1_z; c <= CharMax; c++) {
        // Compute new state.
        auto t = std::vector<size_t>();
        for (auto const x: s)
          for (auto const& [d, u]: nfa.mTable[x].outs)
            if (d == c && !v[u]) {
              t.push_back(u);
              v[u] = true;
            }
        if (t.empty()) continue; // No need to clear `v`: `t` is empty.
        nfa.closure(v, t);
        // Look at the new state:
        auto const it = map.find(v);
        if (it != map.end()) {
          // Already seen.
          dfa.transition(dx, c, it->second);
          for (auto const x: t) v[x] = false; // Clears all bits of `v`.
        } else {
          // Have not seen before, create new DFA node and recurse.
          auto const du = map[v] = dfa.node();
          dfa.transition(dx, c, du);
          for (auto const x: t) v[x] = false; // Clears all bits of `v`.
          dfs(du, t);
        }
      }
    }

    // Main function.
    auto operator()() -> void {
      auto s = std::vector<size_t>();
      v.clear();
      v.resize(nfa.mTable.size());
      map.clear();
      // Initial states.
      s.push_back(nfa.mInitial);
      v[nfa.mInitial] = true;
      nfa.closure(v, s);
      dfa.mInitial = map[v] = dfa.node();
      for (auto const x: s) v[x] = false; // Clears all bits of v.
      dfs(dfa.mInitial, s);
    }
  };

  DFA::DFA(NFA const& nfa) { PowersetConstruction(nfa, *this)(); }

  // Function object for the DFA state minimisation.
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
    std::vector<std::vector<std::pair<Char, size_t>>> rev; // Reverse edges.
    std::vector<Info> info;                                // Identities (class index, pointer to list).
    std::vector<Class> cls;                                // Classes (size, head, is used as distinguisher).
    std::vector<size_t> dists;                             // Indices of classes used as distinguisher sets.
    std::array<std::vector<size_t>, CharMax + 1> srcs;     // Character -> source set.
    std::vector<std::vector<size_t>> intersecting;         // Class index -> list of intersecting states.

    explicit PartitionRefinement(DFA& dfa):
      dfa(dfa) {}

    // Adds DFA node `x` to class `i`, overwriting `info[x]`.
    auto add(size_t x, size_t i) -> void {
      cls[i].size++;
      auto const l = cls[i].head, r = l->r;
      auto const curr = pool.add(List{l, r, x});
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
      auto const head = pool.add(List{nullptr, nullptr, 0});
      head->l = head->r = head;
      auto const index = cls.size();
      cls.push_back(Class{0, head, false});
      return index;
    }

    // Returns (mark -> class ID, number of classes) for the initial partition.
    // One class for each mark, plus one class (Class 0) for nodes that are not marked as accepting states.
    auto initialPartition() -> std::pair<std::unordered_map<Symbol, size_t>, size_t> {
      auto res = std::unordered_map<Symbol, size_t>();
      auto cnt = 1_z; // 0 is reserved for nodes that are not marked as accepting states.
      for (auto const& entry: dfa.mTable)
        if (entry.mark && !res.contains(*entry.mark)) res[*entry.mark] = cnt++;
      return {res, cnt};
    }

    // Main function.
    auto operator()() -> void {
      auto& table = dfa.mTable;
      auto& initial = dfa.mInitial;

      // Add the dead state.
      auto const dead = table.size();
      table.emplace_back();
      auto const n = table.size();

      // Add transitions to dead state.
      // The dead state will have all its out edges pointing to itself.
      for (auto i = 0_z; i < n; i++)
        for (auto c = 1_z; c <= CharMax; c++)
          if (!table[i].outs[c]) table[i].outs[c] = dead;
      // Mid: all elements of `table[i].outs[c]` (for c >= 1) are nonempty.

      // Reverse edges.
      rev.clear();
      rev.resize(n);
      for (auto i = 0_z; i < n; i++)
        for (auto c = 1_z; c <= CharMax; c++) rev[*table[i].outs[c]].emplace_back(c, i);

      // Initial partition.
      auto const& [map, k] = initialPartition();
      cls.clear();
      for (auto i = 0_z; i < k; i++) newClass();
      info.clear();
      info.resize(n);
      for (auto i = 0_z; i < n; i++) {
        if (table[i].mark) add(i, map.at(*table[i].mark));
        else add(i, 0);
      }

      // All initial classes except Class 0 (just not needed) are used as candidate distinguisher sets.
      dists.clear();
      for (auto i = 1_z; i < k; i++) {
        dists.push_back(i);
        cls[i].inDists = true;
      }

      // Partition refinement.
      intersecting.clear();
      while (!dists.empty()) {
        auto const curr = dists.back();
        dists.pop_back();
        cls[curr].inDists = false;

        // Calculate the source sets for all `c`s.
        for (auto c = 1_z; c <= CharMax; c++) srcs[c].clear();
        for (auto p = cls[curr].head->r; p != cls[curr].head; p = p->r) {
          // "Examine transitions" - this occurs a limited number of times, see the long comment.
          // Note that the total size of `srcs[]` equals to this number.
          for (auto const& [c, src]: rev[p->x]) srcs[c].push_back(src);
        }

        for (auto c = 1_z; c <= CharMax; c++) {
          // Inner loop time complexity should be O(size of `srcs[c]`).
          // Mid: all elements of `intersecting[]` are empty.
          intersecting.resize(cls.size());
          for (auto const x: srcs[c]) intersecting[info[x].cid].push_back(x);

          // Now the total size of elements of `intersecting[]` equals to the size of `srcs[c]`.
          for (auto const x: srcs[c]) {
            auto const i = info[x].cid;

            // If intersection is empty or has been processed before...
            if (intersecting[i].empty()) continue;
            // If difference is empty...
            if (intersecting[i].size() == cls[i].size) {
              // Avoid processing multiple times, also does the clearing.
              intersecting[i].clear();
              continue;
            }

            // Create a new class for the "intersection".
            auto const j = newClass();
            // Add elements into it...
            for (auto const y: intersecting[i]) {
              remove(y);
              add(y, j);
            }
            // The original class (with ID = `i`) now becomes the set difference!
            // Avoid processing multiple times, also does the clearing.
            intersecting[i].clear();

            // See which splits will be used as distinguisher sets.
            if (cls[i].inDists || cls[j].size <= cls[i].size) {
              dists.push_back(j);
              cls[j].inDists = true;
            } else { // !cls[i].inDists && cls[i].size < cls[j].size
              dists.push_back(i);
              cls[i].inDists = true;
            }
          }
          // Mid: all elements of `intersecting[]` are empty.
        }
      }

      // Rebuild `table` and `initial`, removing the dead state.
      auto newTable = std::vector<DFA::Entry>(cls.size() - 1);
      auto const newDead = info[dead].cid;
      for (auto i = 0_z; i < table.size(); i++) {
        auto src = info[i].cid;
        if (src == newDead) continue;
        if (src > newDead) src--;
        for (auto c = 1_z; c <= CharMax; c++) {
          auto dst = info[*table[i].outs[c]].cid;
          if (dst == newDead) continue;
          if (dst > newDead) dst--;
          // Build transition.
          newTable[src].outs[c] = dst;
        }
        // Mark accepting state.
        // Also check that a class does not contain different marks.
        assert_always(!newTable[src].mark || newTable[src].mark == table[i].mark);
        newTable[src].mark = table[i].mark;
      }
      table.swap(newTable);
      // DFA should be nonempty.
      initial = info[initial].cid;
      assert_always(initial != newDead);
      if (initial > newDead) initial--;

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

  auto DFA::minimise() -> void { PartitionRefinement (*this)(); }

  auto DFA::match(Generator<Char>& string) const -> std::optional<Symbol> {
    auto last = string.position();
    auto res = std::optional<Symbol>();
    auto s = mInitial;
    // Match greedily, until there are no further possibilities.
    while (!string.eof()) {
      auto const c = string.advance();
      if (!mTable[s].outs[c]) break;
      s = *mTable[s].outs[c];
      // Update longest match, if applicable.
      if (auto const curr = mTable[s].mark) {
        last = string.position();
        res = *curr;
      }
    }
    // Restore last valid position and return.
    string.revert(last);
    return res;
  }

  // Skips the next UTF-8 code point.
  // See: https://en.wikipedia.org/wiki/UTF-8#Encoding
  auto skipCodePoint(Generator<Char>& string) -> bool {
    if (string.eof()) return false;
    string.advance();
    auto last = string.position();
    while (!string.eof()) {
      auto const c = string.advance();
      if ((c & 0b11000000) != 0b10000000) break; // NOLINT(cppcoreguidelines-avoid-magic-numbers)
      last = string.position();
    }
    string.revert(last);
    return true;
  }

  auto Lexer::advance() -> std::optional<Token> {
    auto const last = mString->position();
    if (auto const opt = mAutomaton->match(*mString)) {
      // Success.
      auto const curr = mString->position();
      mPositions.push_back(curr);
      return Token{*opt, last, curr, mString->slice(last, curr)};
    } else {
      // Failure (or reached EOF).
      skipCodePoint(*mString);
      auto const curr = mString->position();
      mPositions.push_back(curr);
      return std::nullopt;
    }
  }

}
