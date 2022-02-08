#include <iostream>
#include <utility>
#include <algorithm>
#include <unordered_map>
#include <core/base.hpp>
#include "parser.hpp"


namespace Parsing {

  // See: https://en.wikipedia.org/wiki/Earley_parser#The_algorithm (for an overview)
  // See: https://loup-vaillant.fr/tutorials/earley-parsing/ (for a simple way to deal with ε rules - TODO)
  // Other related information:
  //   https://github.com/jeffreykegler/kollos/blob/master/notes/misc/leo2.md
  //   https://jeffreykegler.github.io/Marpa-web-site/
  //   https://arxiv.org/pdf/1910.08129.pdf
  // (I am not going to dig too deep into the theories about different parsing algorithms now!)
  vector<vector<EarleyParser::State>> EarleyParser::run(const vector<Token>& str) {
    using std::unordered_map;
    const size_t n = str.size(), m = rules.size();

    // Find the number of nonterminal symbols involved
    TokenID numTokens = start + 1;
    for (const auto& [lhs, rhs]: rules) {
      numTokens = std::max(numTokens, lhs + 1);
      for (Symbol sym: rhs) if (!sym.terminal) numTokens = std::max(numTokens, sym.index + 1);
    }

    // Sort all rules by nonterminal index (for faster access)
    std::sort(rules.begin(), rules.end(), [] (const Rule& a, const Rule& b) { return a.lhs < b.lhs; });
    // For each nonterminal find the index of its first production rule (for faster access, if none then set to `m`)
    // Also accumulate the lengths of RHS (plus one) of the production rules (for better hashing)
    vector<size_t> firstRule(numTokens, m);
    vector<size_t> totalLength(m, 0);
    for (size_t i = 0; i < m; i++) {
      const auto& [lhs, rhs] = rules[i];
      if (firstRule[lhs] == m) firstRule[lhs] = i;
      if (i + 1 < m) totalLength[i + 1] = totalLength[i] + rhs.size() + 1;
    }
    // A hash function for DP states
    auto hash = [&totalLength] (const State& x) {
      return x.leftPos * 524287u + (totalLength[x.ruleIndex] + x.rulePos);
    };

    // The main DP array
    vector<vector<State>> states(n + 1);
    unordered_map<State, size_t, decltype(hash)> mp(0, hash);

    // A minor optimization: avoid looking up rules multiple times (see below)
    vector<TokenID> added;
    vector<bool> isAdded(numTokens);

    // Initial states
    for (size_t i = firstRule[start]; i < m && rules[i].lhs == start; i++) {
      State s{ 0, i, 0 };
      mp[s] = states.size();
      states[0].push_back(s);
    }

    // Invariant: `mp` maps all elements of `states[pos]` to their indices
    for (size_t pos = 0; pos <= n; pos++) {

      // "Completion" stage
      // (This loop will insert new elements in `states[pos]`; don't use range-based for)
      for (size_t i = 0; i < states[pos].size(); i++) {
        const State& s = states[pos][i];
        const auto& derived = rules[s.ruleIndex].rhs;
        if (s.rulePos < derived.size()) continue;

        TokenID sym = rules[s.ruleIndex].lhs;
        for (const State& t: states[s.leftPos]) {
          const auto& tderived = rules[t.ruleIndex].rhs;
          if (t.rulePos < tderived.size() && tderived[t.rulePos] == Symbol{ false, sym }) {
            State tt{ t.leftPos, t.ruleIndex, t.rulePos + 1 };
            if (!mp.contains(tt)) {
              mp[tt] = states.size();
              states[pos].push_back(tt);
            }
          }
        }
      }

      // "Prediction" stage
      // (This loop will insert new elements in `states[pos]`; don't use range-based for)
      for (size_t i = 0; i < states[pos].size(); i++) {
        const State& s = states[pos][i];
        const auto& derived = rules[s.ruleIndex].rhs;
        if (s.rulePos >= derived.size()) continue;

        if (!derived[s.rulePos].terminal) {
          TokenID sym = derived[s.rulePos].index;
          // Avoid looking up rules multiple times...
          if (isAdded[sym]) continue;
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
      }
      // Clear flags
      for (TokenID sym: added) isAdded[sym] = false;
      added.clear();

      // "Scanning" stage
      if (pos >= str.size()) break;
      TokenID tok = str[pos].id;
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
    * ===== A hand-wavey argument for correctness (TODO) =====
    * Every possible derived tree -- if its topmost rule ever gets predicted, then it will be completed!
    * Lemma: every prefix will be reached
    *   Empty: initially true
    *   Prefix + terminal: by scanning
    *   Prefix + non-nullable nonterminal: all its rules are predicted at "prediction" stage -> one of them gets completed later
    *   Prefix + nullable nonterminal: by skipping!
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
