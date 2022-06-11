#include "parser.hpp"
#include <algorithm>
#include <unordered_map>


namespace Parsing {

  using std::unordered_map;
  using std::optional, std::make_optional, std::nullopt;


  bool operator==(const EarleyParser::State& a, const EarleyParser::State& b) {
    return a.startPos == b.startPos && a.rule == b.rule && a.progress == b.progress;
  }

  bool operator==(const EarleyParser::Location& a, const EarleyParser::Location& b) {
    return a.pos == b.pos && a.i == b.i;
  }

  // Parse greedily, until there are no further possibilities.
  // Parsing is considered successful only when the last position contains a completed root symbol.
  bool EarleyParser::nextSentence() {
    if (dirty) {
      process();
      dirty = false;
    }
    optional<ErrorInfo> error;
    while (true) {
      const auto& [found, nextToken] = run();
      if (found) { // Successful parse
        if (sentence.empty()) notimplemented;
        if (error) errors.push_back(*error);
        return true;
      }
      if (!nextToken) { // EOF
        if (!sentence.empty()) { // EOF with incomplete sentence
          if (!error) error = lastError(sentence.back().endPos, sentence.back().endPos, nullopt);
          else error->endPos = sentence.back().endPos;
        }
        if (error) errors.push_back(*error);
        return false;
      }
      // Mid: !index && nextToken
      // Error
      if (!error) error = lastError(nextToken->startPos, nextToken->endPos, patterns.at(nextToken->pattern).first);
      else error->endPos = nextToken->endPos;
      // Skip at least one token to avoid infinite loops
      if (sentence.empty()) {
        auto tok = lexer.nextToken();
        while (tok && patterns.at(tok->pattern).first == ignoredSymbol) tok = lexer.nextToken();
      }
    }
  }

  string EarleyParser::showState(const LinkedState& ls, const vector<string>& names) const {
    const auto& [s, links] = ls;
    string res = std::to_string(s.startPos) + ", <" + names.at(rules[s.rule].lhs.first) + "> ::= ";
    for (size_t i = 0; i < rules[s.rule].rhs.size(); i++) {
      if (i == s.progress) res += "|";
      res += "<" + names.at(rules[s.rule].rhs[i].first) + ">";
    }
    if (s.progress == rules[s.rule].rhs.size()) res += "|";
    res += "\n";
    return res;
  }

  string EarleyParser::showStates(const vector<string>& names) const {
    if (dpa.size() != sentence.size() + 1) unreachable;
    string res = "";
    for (size_t pos = 0; pos <= sentence.size(); pos++) {
      res += "States at position " + std::to_string(pos) + ":\n";
      for (const LinkedState& ls: dpa[pos]) res += showState(ls, names);
      res += "\n";
      if (pos < sentence.size()) res += "Next token: <" + names.at(patterns.at(sentence[pos].pattern).first) + ">\n";
    }
    return res;
  }

  // See: https://en.wikipedia.org/wiki/Earley_parser#The_algorithm (for an overview)
  // See: https://loup-vaillant.fr/tutorials/earley-parsing/ (for a possible way to deal with empty rules)
  // Other related information:
  //   https://github.com/jeffreykegler/kollos/blob/master/notes/misc/leo2.md
  //   https://jeffreykegler.github.io/Marpa-web-site/
  //   https://arxiv.org/pdf/1910.08129.pdf
  // (I am not going to dig too deep into the theories about different parsing algorithms now!)

  void EarleyParser::process() {

    // Find the number of symbols involved.
    numSymbols = startSymbol + 1;
    for (const auto& [lhs, rhs]: rules) {
      numSymbols = std::max(numSymbols, lhs.first + 1);
      for (const auto& r: rhs) numSymbols = std::max(numSymbols, r.first + 1);
    }

    // Find all empty rules, and confirm that no other rules are nullable.
    // It is quite possible to support arbitrary nullable rules, but that would make things significantly messier
    // (just think about ambiguous empty derivations...)
    emptyRule = vector<optional<size_t>>(numSymbols, nullopt);
    for (size_t i = 0; i < rules.size(); i++) {
      const auto& [lhs, rhs] = rules[i];
      if (rhs.empty()) emptyRule[lhs.first] = i;
    }
    for (size_t i = 0; i < rules.size(); i++) {
      const auto& [lhs, rhs] = rules[i];
      if (emptyRule[lhs.first] != i) {
        bool f = false;
        for (const auto& r: rhs) if (!emptyRule[r.first]) f = true;
        if (!f) notimplemented;
      }
    }

    // Sort all non-empty (non-nullable) rules by symbol ID (for faster access in `run()`).
    // Also accumulate the lengths of RHS (plus one) of the production rules (for better hashing in `run()`)
    sorted.clear();
    totalLength.clear();
    totalLength.push_back(0);
    for (size_t i = 0; i < rules.size(); i++) {
      const auto& [lhs, rhs] = rules[i];
      if (emptyRule[lhs.first] != i) sorted.push_back(i);
      totalLength.push_back(totalLength[i] + rhs.size() + 1);
    }
    std::sort(sorted.begin(), sorted.end(), [this] (size_t i, size_t j) { return rules[i].lhs < rules[j].lhs; });
    size_t n = sorted.size();

    // For each symbol find the index of its first production rule (for faster access in `run()`, if none then set to `n`)
    firstRule = vector<size_t>(numSymbols, n);
    for (size_t i = 0; i < n; i++) {
      const auto& [lhs, rhs] = rules[sorted[i]];
      if (firstRule[lhs.first] == n) firstRule[lhs.first] = i;
    }
  }

  // Pre: `numSymbols`, `emptyRule`, `sorted`, `firstRule` and `totalLength` must be consistent with current rules.
  // Post: `sentence` and `dpa` contains the parsing result. Returns { index, nextToken }.
  pair<bool, optional<Token>> EarleyParser::run() {
    if (!startSymbol) notimplemented;

    sentence.clear();
    dpa.clear();

    // A minor optimization: avoid looking up rules multiple times (see below)
    vector<Symbol> added;
    vector<bool> isAdded(numSymbols, false);

    // A hash function for DP states, for mapping states back to indices
    auto hash = [this] (const State& x) { return x.startPos * 524287u + (totalLength[x.rule] + x.progress); };
    unordered_map<State, size_t, decltype(hash)> mp(0, hash);

    // Initial states
    dpa.emplace_back();
    for (size_t i = firstRule[startSymbol]; i < sorted.size() && rules[sorted[i]].lhs.first == startSymbol; i++) {
      State s{ 0, sorted[i], 0 };
      mp[s] = dpa[0].size();
      dpa[0].push_back(LinkedState{ s, {} });
    }
    optional<Token> nextToken = nullopt;

    // Invariant: `mp` maps all `state`s of items of `dpa[pos]` to the items' indices
    for (size_t pos = 0; ; pos++) {

      #define ensure(s) \
        if (!mp.contains(s)) { \
          mp[s] = dpa[pos].size(); \
          dpa[pos].push_back(LinkedState{ s, {} }); \
        }

      // "Prediction/completion" stage
      for (size_t i = 0; i < dpa[pos].size(); i++) {
        State s = dpa[pos][i].state;
        const auto& [lhs, rhs] = rules[s.rule];
        if (s.progress < rhs.size()) {
          // Perform prediction
          const auto& [sym, prec] = rhs[s.progress];
          if (!isAdded[sym]) {
            isAdded[sym] = true;
            added.push_back(sym);
            for (size_t j = firstRule[sym]; j < sorted.size() && rules[sorted[j]].lhs.first == sym; j++) {
              State u{ pos, sorted[j], 0 };
              ensure(u);
            }
          }
          // Perform empty completion (if `sym` is nullable, we could skip it)
          if (emptyRule[sym] && prec <= rules[*emptyRule[sym]].lhs.second) {
            State t{ pos, *emptyRule[sym], 0 };
            State u{ s.startPos, s.rule, s.progress + 1 };
            ensure(t);
            ensure(u);
            dpa[pos][mp[u]].links.push_back({ { pos, i }, { pos, mp[t] } });
          }
        } else {
          // Perform nonempty completion
          size_t tpos = s.startPos;
          if (tpos == pos) continue;
          const auto& [sym, prec] = lhs;
          for (size_t j = 0; j < dpa[tpos].size(); j++) {
            State t = dpa[tpos][j].state;
            const auto& trhs = rules[t.rule].rhs;
            if (t.progress < trhs.size() && trhs[t.progress].first == sym && trhs[t.progress].second <= prec) {
              State u{ t.startPos, t.rule, t.progress + 1 };
              ensure(u);
              dpa[pos][mp[u]].links.push_back({ { tpos, j }, { pos, i } });
            }
          }
        }
      }
      // Clear flags
      for (Symbol sym: added) isAdded[sym] = false;
      added.clear();

      #undef ensure

      // Advance to next position
      size_t restore = lexer.position();
      nextToken = lexer.nextToken();
      while (nextToken && patterns.at(nextToken->pattern).first == ignoredSymbol) nextToken = lexer.nextToken();
      if (!nextToken) break; // EOF
      sentence.push_back(*nextToken);

      // "Scanning" stage
      // Also updating `mp` to reflect `states[pos + 1]` instead (re-establish loop invariant)
      dpa.emplace_back();
      mp.clear();
      const auto& [sym, prec] = patterns.at(nextToken->pattern);
      for (size_t i = 0; i < dpa[pos].size(); i++) {
        State s = dpa[pos][i].state;
        const auto& rhs = rules[s.rule].rhs;
        if (s.progress < rhs.size() && rhs[s.progress].first == sym && rhs[s.progress].second <= prec) {
          State u{ s.startPos, s.rule, s.progress + 1 };
          // No need to check for presence! `s` is already unique.
          mp[u] = dpa[pos + 1].size();
          dpa[pos + 1].push_back(LinkedState{ u, { { { pos, i }, Leaf } } });
        }
      }

      // If no more possibilities then restore and stop
      if (dpa[pos + 1].empty()) {
        lexer.setPosition(restore);
        sentence.pop_back(); dpa.pop_back();
        break;
      }
    }

    // Check if the start symbol completes
    if (dpa.size() != sentence.size() + 1) unreachable;
    size_t pos = sentence.size();
    bool found = false;
    for (size_t i = 0; i < dpa[pos].size(); i++) {
      State s = dpa[pos][i].state;
      const auto& [lhs, rhs] = rules[s.rule];
      if (lhs.first == startSymbol && s.startPos == 0 && s.progress == rhs.size()) found = true;
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
    *       - nonempty nonterminal: by IH (2), the prefix minus the last symbol will be reached
    *         -> all rules for the last symbol get predicted at the corresponding position
    *         -> by IH (1), the correct one will get completed in a later position, advancing the current item.
    *       If the rule yields empty string, it may have been completed earlier, and the current item
    *       does not have a chance to advance... That's why we need the final case:
    *       - empty nonterminal: by IH (2) + skipping at the "prediction/completion" stage.
    *
    * ===== A hand-wavey argument for time complexity =====
    * For each iteration of the outer loop:
    *   Number of states (i.e. `dpa[pos].size()`) = O(|G|n)
    *   Prediction = O(|G|n) (iterating through states = O(|G|n), total states added = O(|G|))
    *   Completion = O(|G|²n²) (iterating though states = O(|G|n), time for each state = O(|G|n))
    *              = O(|G|n) for unambiguous (iterating through states = O(|G|n), total states added = O(|G|n))
    *   Scanning   = O(|G|n) (iterating through states = O(|G|n))
    * Overall: O(|G|²n³)
    *          O(|G|n²) for unambiguous (*)
    */

    return { found, nextToken };
  }

  // For use in `nextSentence()` only
  auto EarleyParser::lastError(size_t startPos, size_t endPos, const optional<Symbol>& got) const -> ErrorInfo {
    if (dpa.size() != sentence.size() + 1) unreachable;
    size_t pos = sentence.size();
    vector<Symbol> expected;
    for (const LinkedState& ls: dpa[pos]) {
      const State& s = ls.state;
      const auto& [lhs, rhs] = rules[s.rule];
      if (s.progress < rhs.size()) expected.push_back(rhs[s.progress].first);
    }
    std::sort(expected.begin(), expected.end());
    expected.resize(std::unique(expected.begin(), expected.end()) - expected.begin());
    return { startPos, endPos, expected, got };
  }

}
