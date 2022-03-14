#include <iostream>
#include <utility>
#include <algorithm>
#include <unordered_map>
#include <core/base.hpp>
#include "parser.hpp"


namespace Parsing {

  // See: https://en.wikipedia.org/wiki/Earley_parser#The_algorithm (for an overview)
  // See: https://loup-vaillant.fr/tutorials/earley-parsing/ (for a simple way to deal with ε rules)
  // Other related information:
  //   https://github.com/jeffreykegler/kollos/blob/master/notes/misc/leo2.md
  //   https://jeffreykegler.github.io/Marpa-web-site/
  //   https://arxiv.org/pdf/1910.08129.pdf
  // (I am not going to dig too deep into the theories about different parsing algorithms now!)
  vector<vector<EarleyParser::State>> EarleyParser::run(const vector<Token>& str) {
    using std::unordered_map;
    const size_t n = str.size(), m = rules.size();

    // Find the number `k` of nonterminal symbols involved
    TokenID k = start + 1;
    for (const auto& [lhs, rhs]: rules) {
      k = std::max(k, lhs + 1);
      for (Symbol sym: rhs) if (!sym.terminal) k = std::max(k, sym.index + 1);
    }
    // Work out "nullable" nonterminals (O(|G|²))
    vector<bool> nullable(k, false);
    bool updates = false;
    do {
      updates = false;
      for (const auto& [lhs, rhs]: rules) if (!nullable[lhs]) {
        bool f = true;
        for (auto [terminal, index]: rhs) {
          if (terminal || !nullable[index]) { f = false; break; }
        }
        if (f) {
          nullable[lhs] = true;
          updates = true;
        }
      }
    } while (updates);

    // Sort all rules by nonterminal index (for faster access)
    std::sort(rules.begin(), rules.end(), [] (const Rule& a, const Rule& b) { return a.lhs < b.lhs; });
    // For each nonterminal find the index of its first production rule (for faster access, if none then set to `m`)
    // Also accumulate the lengths of RHS (plus one) of the production rules (for better hashing)
    vector<size_t> firstRule(k, m);
    vector<size_t> totalLength(m, 0);
    for (size_t i = 0; i < m; i++) {
      const auto& [lhs, rhs] = rules[i];
      if (firstRule[lhs] == m) firstRule[lhs] = i;
      if (i + 1 < m) totalLength[i + 1] = totalLength[i] + rhs.size() + 1;
    }

    // The main DP array
    /*
    struct Entry {
      State state;
      size_t prevPos, prevIndex;
      size_t childPos, childIndex;
    };
    */
    vector<vector<State>> states(n + 1);

    // A hash function for DP states
    auto hash = [&totalLength] (const State& x) {
      return x.leftPos * 524287u + (totalLength[x.ruleIndex] + x.rulePos);
    };
    unordered_map<State, size_t, decltype(hash)> mp(0, hash);

    // A minor optimization: avoid looking up rules multiple times (see below)
    vector<TokenID> added;
    vector<bool> isAdded(k);

    // Initial states
    for (size_t i = firstRule[start]; i < m && rules[i].lhs == start; i++) {
      State s{ 0, i, 0 };
      mp[s] = states.size();
      states[0].push_back(s);
    }

    // Invariant: `mp` maps all elements of `states[pos]` to their indices
    for (size_t pos = 0; pos <= n; pos++) { 

      // "Prediction/completion" stage
      // (This loop will insert new elements in `states[pos]`; don't use range-based for)
      for (size_t i = 0; i < states[pos].size(); i++) {
        State s = states[pos][i];
        const auto& derived = rules[s.ruleIndex].rhs;

        if (s.rulePos < derived.size()) {
          // Perform prediction
          if (derived[s.rulePos].terminal) continue;
          TokenID sym = derived[s.rulePos].index;
          // Avoid looking up rules multiple times...
          if (!isAdded[sym]) {
            isAdded[sym] = true;
            added.push_back(sym);
            // Add all rules for `sym`
            for (size_t j = firstRule[sym]; j < m && rules[j].lhs == sym; j++) {
              State ss{ pos, j, 0 };
              if (!mp.contains(ss)) {
                mp[ss] = states.size();
                states[pos].push_back(ss);
              }
            }
          }
          // If `sym` is nullable, we could skip it (early completion)
          if (nullable[sym]) {
            State ss{ pos, s.ruleIndex, s.rulePos + 1 };
            if (!mp.contains(ss)) {
              mp[ss] = states.size();
              states[pos].push_back(ss);
            } else std::cout << "Ambiguity detected" << std::endl; // TEMP CODE
          }
        } else {
          // Perform nonempty completion
          if (rules[s.ruleIndex].rhs.empty()) continue;
          TokenID sym = rules[s.ruleIndex].lhs;
          // (TODO: optimize this loop for better time complexity bounds on unambiguous grammars?)
          // (Or maybe too many heap allocations will make it slower in practice?)
          for (size_t j = 0; j < states[s.leftPos].size(); j++) {
            State t = states[s.leftPos][j];
            const auto& tderived = rules[t.ruleIndex].rhs;
            if (t.rulePos < tderived.size() && tderived[t.rulePos] == Symbol{ false, sym }) {
              State tt{ t.leftPos, t.ruleIndex, t.rulePos + 1 };
              if (!mp.contains(tt)) {
                mp[tt] = states.size();
                states[pos].push_back(tt);
              } else std::cout << "Ambiguity detected" << std::endl; // TEMP CODE
            }
          }
        }
      }
      // Clear flags
      for (TokenID sym: added) isAdded[sym] = false;
      added.clear();

      if (pos >= str.size()) break;
      TokenID tok = str[pos].id;

      // "Scanning" stage
      // Also updating `mp` to reflect `states[pos + 1]` instead
      mp.clear();
      for (const State& s: states[pos]) {
        const auto& derived = rules[s.ruleIndex].rhs;
        if (s.rulePos < derived.size() && derived[s.rulePos] == Symbol{ true, tok }) {
          State ss{ s.leftPos, s.ruleIndex, s.rulePos + 1 };
          // No need to check presence! `s` is already unique.
          mp[ss] = states[pos + 1].size();
          states[pos + 1].emplace_back(ss);
        }
      }

    }

    /*
    * ===== A hand-wavey argument for correctness =====
    * By induction (1):
    *     If a (possibly empty) substring has a derivation tree, and the root node of the tree
    *     was predicted at the starting position of that substring (in the "prediction/completion" stage),
    *     then the root node will get completed (i.e. the completed item will be added to the DP array),
    *     no later than the "prediction/completion" stage performed at the end position.
    *   By induction (2):
    *       Every prefix of the root production rule will be reached, no later than the
    *       "prediction/completion" stage performed at the corresponding position.
    *     Base case (empty prefix): initially true.
    *     Induction step: if last symbol is...
    *       - terminal: by IH (2) + "scanning" stage (pos-1 ~ pos) is before "prediction/completion" stage (pos)
    *       - non-nullable nonterminal: by IH (2), the prefix minus the last symbol will be reached
    *         -> all rules for the last symbol get predicted at the corresponding position
    *         -> by IH (1), the correct one will get completed in a later position, advancing the current item.
    *       If the rule yields empty string, it may have been completed earlier, and the current item
    *       does not have a chance to advance... That's why we need the final case:
    *       - nullable nonterminal: by IH(2) + skipping at the "prediction/completion" stage.
    * 
    * ===== A hand-wavey argument for time complexity =====
    * For each iteration of the outer loop:
    *   Number of states (i.e. `states[pos].size()`) = O(|G|n)
    *   Prediction = O(|G|n) (iterating through states = O(|G|n), total states added = O(|G|))
    *   Completion = O(|G|²n²) (iterating though states = O(|G|n), time for each state = O(|G|n))
    *              = O(|G|n) for unambiguous (iterating through states = O(|G|n), total states added = O(|G|n))
    *   Scanning   = O(|G|n) (iterating through states = O(|G|n))
    * Overall: O(|G|²n³)
    *          O(|G|n²) for unambiguous
    */

    return states;
  }

  string EarleyParser::showState(const State& s, const vector<string>& terminals, const vector<string>& nonterminals) const {
    string res = std::to_string(s.leftPos) + ", " + nonterminals.at(rules[s.ruleIndex].lhs) + " ::= ";
    for (size_t i = 0; i < rules[s.ruleIndex].rhs.size(); i++) {
      if (i == s.rulePos) res += "|";
      Symbol sym = rules[s.ruleIndex].rhs[i];
      res += sym.terminal? "[" + terminals.at(sym.index) + "]" : "<" + nonterminals.at(sym.index) + ">";
    }
    if (s.rulePos == rules[s.ruleIndex].rhs.size()) res += "|";
    return res;
  }

}
