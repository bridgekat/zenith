#include "parser.hpp"
#include <algorithm>
#include <ranges>
#include <unordered_map>

// TEMP CODE
#include <iostream>

namespace Parsing {

  auto CFG::process() -> void {
    // Count the number of symbols involved.
    numSymbols = startSymbol + 1;
    for (auto const& [lhs, rhs]: rules) {
      numSymbols = std::max(numSymbols, lhs.first + 1);
      for (auto const& r: rhs) numSymbols = std::max(numSymbols, r.first + 1);
    }

    // Find all empty rules, and confirm that no other rules are nullable.
    // It is quite possible to support arbitrary nullable rules, but that would make things significantly messier
    // (just think about ambiguous empty derivations...)
    emptyRule = std::vector<std::optional<size_t>>(numSymbols);
    for (auto i = 0_z; i < rules.size(); i++) {
      auto const& [lhs, rhs] = rules[i];
      if (rhs.empty()) emptyRule[lhs.first] = i;
    }
    for (auto i = 0_z; i < rules.size(); i++) {
      auto const& [lhs, rhs] = rules[i];
      if (emptyRule[lhs.first] != i) {
        auto nonNullable = false;
        for (auto const& r: rhs)
          if (!emptyRule[r.first]) nonNullable = true;
        // Confirm that no other rules are nullable.
        assert_always(nonNullable);
      }
    }
    // Nullable start symbol can cause infinite loop.
    assert_always(!emptyRule[startSymbol]);

    // Sort all non-empty (non-nullable) rules by symbol ID (for faster access).
    // Also accumulate the lengths of RHS (plus one) of the production rules (for better hashing).
    sorted.clear();
    for (auto i = 0_z; i < rules.size(); i++) {
      auto const& [lhs, rhs] = rules[i];
      if (emptyRule[lhs.first] != i) sorted.push_back(i);
    }
    std::sort(sorted.begin(), sorted.end(), [this](size_t i, size_t j) { return rules[i].lhs < rules[j].lhs; });
    auto const n = sorted.size();

    // For each symbol find the index of its first production rule (for faster access).
    // If none then set to `n`.
    firstRule = std::vector<size_t>(numSymbols, n);
    for (auto i = 0_z; i < n; i++) {
      auto const& [lhs, rhs] = rules[sorted[i]];
      if (firstRule[lhs.first] == n) firstRule[lhs.first] = i;
    }
  }

  auto EarleyParser::advance() -> bool {
    if (_run()) {
      // Success.
      return true;
    } else if (auto const token = _nextToken()) {
      // Failure.
      // TEMP CODE
      std::cerr << "ERROR" << std::endl;
      return false;
    } else {
      // Reached EOF.
      return false;
    }
    /*
    auto error = std::optional<ParserError>();
    while (!) {
      auto const found = run();
      if (found) {
        // Successful parse.
        if (_sentence.empty()) unimplemented;
        if (error) mErrors.push_back(*error);
        return true;
      }
      if (!nextToken) {
        // EOF.
        if (!_sentence.empty()) {
          // EOF with incomplete sentence.
          if (!error) error = lastError(_sentence.back().endPos, _sentence.back().endPos, std::nullopt);
          else error->endPos = _sentence.back().endPos;
        }
        if (error) mErrors.push_back(*error);
        return false;
      }
      // Mid: !index && nextToken
      // Error.
      if (!error) error = lastError(nextToken->startPos, nextToken->endPos, mPatterns.at(nextToken->id).sym.first);
      else error->endPos = nextToken->endPos;
      // Skip at least one token to avoid infinite loops.
      if (_sentence.empty()) {
        auto tok = mLexer->advance();
        while (tok && mPatterns.at(tok->id).sym.first == mIgnoredSymbol) tok = mLexer->advance();
      }
    }
    */
  }

  auto EarleyParser::showState(Node const& ls, std::vector<std::string> const& names) const -> std::string {
    auto const& rules = _grammar->rules;
    auto const& [s, links] = ls;
    auto res = std::to_string(s.startPos) + ", <" + names.at(rules[s.rule].lhs.first) + "> ::= ";
    for (auto i = 0_z; i < rules[s.rule].rhs.size(); i++) {
      if (i == s.progress) res += "|";
      res += "<" + names.at(rules[s.rule].rhs[i].first) + ">";
    }
    if (s.progress == rules[s.rule].rhs.size()) res += "|";
    res += "\n";
    return res;
  }

  auto EarleyParser::showStates(std::vector<std::string> const& names) const -> std::string {
    assert_always(_forest.size() == _sentence.size() + 1);
    auto res = std::string();
    for (auto pos = 0_z; pos <= _sentence.size(); pos++) {
      res += "States at position " + std::to_string(pos) + ":\n";
      for (auto const& ls: _forest[pos]) res += showState(ls, names);
      res += "\n";
      if (pos < _sentence.size()) res += "Next token: <" + names.at(_sentence[pos].id) + ">\n";
    }
    return res;
  }

  // Earley's parsing algorithm.
  // This is more suitable for left-recursive grammars than right-recursive ones.
  // See: https://en.wikipedia.org/wiki/Earley_parser#The_algorithm for an overview.
  // See: https://loup-vaillant.fr/tutorials/earley-parsing/ for a possible way to deal with empty rules.
  // Other related information:
  // - https://github.com/jeffreykegler/kollos/blob/master/notes/misc/leo2.md
  // - https://jeffreykegler.github.io/Marpa-web-site/
  // - https://arxiv.org/pdf/1910.08129.pdf
  //
  // Pre: `_grammar` has been preprocessed.
  // Returns `true` on success. In this case `_sentence` and `_forest` will contain the parsing result.
  auto EarleyParser::_run() -> bool {
    auto const& rules = _grammar->rules;
    auto const startSymbol = _grammar->startSymbol;
    auto const numSymbols = _grammar->numSymbols;
    auto const& emptyRule = _grammar->emptyRule;
    auto const& sorted = _grammar->sorted;
    auto const& firstRule = _grammar->firstRule;

    auto last = _generator->position();
    auto lastIndex = 0_z;
    auto res = false;

    _sentence.clear();
    _forest.clear();
    _map.clear();
    _completions.clear();

    // Minor optimization: avoid looking up rules multiple times (see below).
    auto addedSym = std::vector<Symbol>();
    auto symAdded = std::vector<bool>(numSymbols);

    // Initial states.
    _forest.emplace_back();
    for (auto i = firstRule[startSymbol]; i < sorted.size() && rules[sorted[i]].lhs.first == startSymbol; i++) {
      auto const s = State{0, 0, sorted[i], 0};
      _forest[0].push_back(Node{s, {}});
      _map[s] = &_forest[0].back();
    }

    // Parse greedily, until there are no further possibilities.
    // Inv: `map` maps all `State`s of items to the items' addresses.
    for (auto pos = 0_z; !_forest[pos].empty(); pos++) {

      // "Prediction/completion" stage.
      for (auto i = 0_z; i < _forest[pos].size(); i++) {
        // Note that `std::deque::push_back()` invalidates iterators, but not references.
        // See: https://en.cppreference.com/w/cpp/container/deque/push_back
        auto const ps = &_forest[pos][i];
        auto const& s = ps->state;
        auto const& [sl, sr] = rules[s.rule];
        if (s.progress < sr.size()) {
          // Perform nonempty prediction.
          auto const& [sym, prec] = sr[s.progress];
          if (!symAdded[sym]) {
            symAdded[sym] = true;
            addedSym.push_back(sym);
            for (auto j = firstRule[sym]; j < sorted.size() && rules[sorted[j]].lhs.first == sym; j++) {
              auto const u = State{pos, pos, sorted[j], 0};
              _add(pos, u);
            }
          }
          // Add to completion candidates.
          _completions.emplace(std::pair(pos, sr[s.progress].first), ps);
          // Perform empty prediction + completion (if `sym` is nullable, we could skip it).
          if (auto const emp = emptyRule[sym]; emp && prec <= rules[*emp].lhs.second) {
            auto const t = State{pos, pos, *emp, 0};
            auto const u = State{s.startPos, pos, s.rule, s.progress + 1};
            _add(pos, u)->links.push_back({ps, _add(pos, t)});
          }
        } else if (s.startPos < pos) {
          // Perform nonempty completion.
          auto const& [sym, prec] = sl;
          auto const& [first, last] = _completions.equal_range(std::pair(s.startPos, sym));
          for (auto const& [_, pt]: std::ranges::subrange(first, last)) {
            auto const& t = pt->state;
            auto const& [tl, tr] = rules[t.rule];
            assert_always(t.progress < tr.size() && tr[t.progress].first == sym);
            if (tr[t.progress].second <= prec) {
              auto const u = State{t.startPos, pos, t.rule, t.progress + 1};
              _add(pos, u)->links.push_back({pt, ps});
            }
          }
        }
      }
      // Clear flags.
      for (auto const i: addedSym) symAdded[i] = false;
      addedSym.clear();

      // Check if the start symbol completes and update result.
      auto found = false;
      for (auto i = 0_z; i < _forest[pos].size(); i++) {
        auto const& s = _forest[pos][i].state;
        auto const& [lhs, rhs] = rules[s.rule];
        if (lhs.first == startSymbol && s.startPos == 0 && s.progress == rhs.size()) found = true;
      }
      if (found) {
        last = _generator->position();
        lastIndex = pos;
        res = true;
      }

      // Advance to next position.
      auto const& token = _nextToken();
      if (!token) break; // EOF.

      // "Scanning" stage.
      _sentence.push_back(*token);
      _forest.emplace_back();
      _map.clear();
      auto const& [sym, prec] = std::pair(token->id, PrecedenceMax);
      for (auto i = 0_z; i < _forest[pos].size(); i++) {
        auto const ps = &_forest[pos][i];
        auto const& s = ps->state;
        auto const& [sl, sr] = rules[s.rule];
        if (s.progress < sr.size() && sr[s.progress].first == sym && sr[s.progress].second <= prec) {
          // Perform single-token shift.
          auto const u = State{s.startPos, pos + 1, s.rule, s.progress + 1};
          _add(pos + 1, u)->links.push_back({ps, &_sentence.back()});
        }
      }
    }

    // Restore last valid position and return.
    _generator->revert(last);
    _sentence.resize(lastIndex);
    _forest.resize(lastIndex + 1);
    return res;

    /*
     * ===== A hand-wavey argument for correctness =====
     * By induction prove (1):
     *     If a (possibly empty) substring has a derivation tree, and the root node of the tree
     *     was predicted at the starting position of that substring (in the "prediction/completion" stage),
     *     then the root node will get completed (i.e. the completed item will be added to the DP array),
     *     no later than the "prediction/completion" stage performed at the end position.
     * - By induction prove (2):
     *       Every prefix of the root production rule will be reached, no later than the
     *       "prediction/completion" stage performed at the corresponding position.
     *   - Base case (empty prefix): initially true.
     *   - Induction step: if last symbol is...
     *     - terminal: by IH of (2) + "scanning" stage (pos-1 ~ pos) is before "prediction/completion" stage (pos)
     *     - nonempty nonterminal: by IH of (2), the prefix minus the last symbol will be reached
     *       -> all rules for the last symbol get predicted at the corresponding position
     *       -> by IH of (1), the correct one will get completed in a later position, advancing the current item.
     *     If the rule yields empty string, it may have been completed earlier, and the current item
     *     does not have a chance to advance... That's why we need the final case:
     *     - empty nonterminal: by IH of (2) + skipping at the "prediction/completion" stage.
     *
     * ===== A hand-wavey argument for time complexity =====
     * Number of states on each position (i.e. `forest[pos].size()`) = O(|G|n).
     * If grammar is unambiguous, each state can have at most one link.
     * For each iteration of the outer loop:
     * - Prediction = O(|G|n) (iterating through states = O(|G|n), total states added = O(|G|)).
     * - Completion = O(|G|²n²) (iterating though states = O(|G|n), time for each state = O(|G|n)).
     *              = O(|G|n) for unambiguous cases (iterating through states = O(|G|n), total links added = O(|G|n)).
     * - Scanning   = O(|G|n) (iterating through states = O(|G|n)).
     *
     * Overall: O(|G|²n³) for all cases;
     *          O(|G|n²) for unambiguous cases.
     */
  }

  // For use in `nextSentence()` only.
  /*
  auto EarleyParser::lastError(size_t startPos, size_t endPos, std::optional<Symbol> const& got) const -> ParserError {
    assert_always(_forest.size() == _sentence.size() + 1);
    auto pos = _sentence.size();
    auto expected = std::vector<Symbol>();
    for (auto const& ls: mDP[pos]) {
      auto const& s = ls.state;
      auto const& [lhs, rhs] = rules[s.rule];
      if (s.progress < rhs.size()) expected.push_back(rhs[s.progress].first);
    }
    std::sort(expected.begin(), expected.end());
    expected.resize(static_cast<size_t>(std::unique(expected.begin(), expected.end()) - expected.begin()));
    return {startPos, endPos, expected, got};
  }
  */

}
