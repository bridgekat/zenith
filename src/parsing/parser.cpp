#include "parser.hpp"
#include <algorithm>
#include <unordered_map>

// TEMP CODE
#include <iostream>

namespace Parsing {

  auto GrammarBuilder::withStartSymbol(Symbol value) -> GrammarBuilder& {
    _startSymbol = value;
    return *this;
  }
  auto GrammarBuilder::withIgnoredSymbol(Symbol value) -> GrammarBuilder& {
    _ignoredSymbol = value;
    return *this;
  }
  auto GrammarBuilder::withRule(
    std::pair<Symbol, Precedence> lhs,
    std::vector<std::pair<Symbol, Precedence>> const& rhs
  ) -> GrammarBuilder& {
    _rules.push_back(Grammar::Rule{lhs, rhs});
    return *this;
  }

  auto GrammarBuilder::make() -> Grammar const {
    auto res = Grammar();
    auto& numSymbols = res.numSymbols;
    auto& startSymbol = res.startSymbol = _startSymbol;
    auto& ignoredSymbol = res.ignoredSymbol = _ignoredSymbol;
    auto& rules = res.rules = _rules;
    auto& sorted = res.sorted;
    auto& ranges = res.ranges;

    // Number of rules.
    auto const n = rules.size();

    // Count the number of symbols involved.
    numSymbols = std::max(startSymbol, ignoredSymbol);
    for (auto const& [lhs, rhs]: rules) {
      numSymbols = std::max(numSymbols, lhs.first);
      for (auto const& r: rhs) numSymbols = std::max(numSymbols, r.first);
    }
    numSymbols++;

    // Sort all rules by LHS symbol ID (for faster access).
    sorted.clear();
    for (auto i = 0_z; i < n; i++) sorted.push_back(i);
    std::sort(sorted.begin(), sorted.end(), [&rules](size_t i, size_t j) { return rules[i].lhs < rules[j].lhs; });

    // For each symbol ID find the index range of its production rules in `sorted` (for faster access).
    // If none then all set to n.
    ranges = std::vector<Grammar::IndexRange>(numSymbols, {n, n});
    for (auto i = 0_z; i < n; i++) {
      auto const& curr = rules[sorted[i]].lhs.first;
      if (i == 0 || rules[sorted[i - 1]].lhs.first != curr) ranges[curr].begin = i;
      if (i == n - 1 || rules[sorted[i + 1]].lhs.first != curr) ranges[curr].end = i + 1;
    }
    return res;
  }

  auto Parser::advance() -> bool {
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
        if (_tokens.empty()) unimplemented;
        if (error) mErrors.push_back(*error);
        return true;
      }
      if (!nextToken) {
        // EOF.
        if (!_tokens.empty()) {
          // EOF with incomplete sentence.
          if (!error) error = lastError(_tokens.back().end, _tokens.back().end, std::nullopt);
          else error->end = _tokens.back().end;
        }
        if (error) mErrors.push_back(*error);
        return false;
      }
      // Mid: !index && nextToken
      // Error.
      if (!error) error = lastError(nextToken->begin, nextToken->end, mPatterns.at(nextToken->id).sym.first);
      else error->end = nextToken->end;
      // Skip at least one token to avoid infinite loops.
      if (_tokens.empty()) {
        auto tok = mLexer->advance();
        while (tok && mPatterns.at(tok->id).sym.first == mIgnoredSymbol) tok = mLexer->advance();
      }
    }
    */
  }

  auto Parser::showState(Node const& node, std::vector<std::string> const& names) const -> std::string {
    auto const& rules = _grammar.rules;
    auto const& s = node.state;
    auto res = std::to_string(s.begin) + ", <" + names.at(rules[s.rule].lhs.first) + "> ::= ";
    for (auto i = 0_z; i < rules[s.rule].rhs.size(); i++) {
      if (i == s.progress) res += "|";
      res += "<" + names.at(rules[s.rule].rhs[i].first) + ">";
    }
    if (s.progress == rules[s.rule].rhs.size()) res += "|";
    res += "\n";
    return res;
  }

  auto Parser::showStates(std::vector<std::string> const& names) const -> std::string {
    assert(_nodes.size() == _tokens.size() + 1);
    auto res = std::string();
    for (auto pos = 0_z; pos <= _tokens.size(); pos++) {
      res += "States at position " + std::to_string(pos) + ":\n";
      for (auto const& mode: _nodes[pos]) res += showState(mode, names);
      res += "\n";
      if (pos < _tokens.size()) res += "Next token: <" + names.at(_tokens[pos].id) + ">\n";
    }
    return res;
  }

  // Returns next non-ignored token, or `std::nullopt` if reaches EOF.
  auto Parser::_nextToken() -> std::optional<Token> {
    while (!_lexer.eof()) {
      auto const token = _lexer.advance();
      if (token && token->id != _grammar.ignoredSymbol) return token;
    }
    return {};
  }

  // Adds a node with state `state` to `_nodes` while registering it in `_map`.
  // If a node with the given state is already added, returns a pointer to it.
  auto Parser::_node(size_t begin, size_t end, size_t rule, size_t progress) -> Node* {
    auto const state = Node::State{begin, end, rule, progress};
    if (auto const it = _map.find(state); it != _map.end()) return it->second;
    _nodes[end].push_back(Node{state, {}, {}});
    return _map[state] = &_nodes[end].back();
  }

  // Adds a transition from `prev` to `next` which goes through `child`.
  // This adds both forward and backward links.
  auto Parser::_transition(Node* prev, std::variant<Node*, Token*> child, Node* next) -> void {
    prev->next.emplace_back(next, child);
    next->prev.emplace_back(prev, child);
  }

  // Earley's parsing algorithm.
  // See: https://en.wikipedia.org/wiki/Earley_parser#The_algorithm for an overview.
  // See: https://loup-vaillant.fr/tutorials/earley-parsing
  // Other related information:
  // - https://github.com/jeffreykegler/old_kollos/blob/master/notes/misc/leo2.md (TODO)
  // - https://jeffreykegler.github.io/Marpa-web-site/
  // - https://arxiv.org/pdf/1910.08129.pdf
  //
  // Pre: `_grammar` is well-formed.
  // Returns `true` on success. In this case `_tokens` and `_nodes` will contain the parsing result.
  auto Parser::_run() -> bool {
    auto const& rules = _grammar.rules;
    auto const& startSymbol = _grammar.startSymbol;
    auto const& numSymbols = _grammar.numSymbols;
    auto const& sorted = _grammar.sorted;
    auto const& ranges = _grammar.ranges;

    auto last = _lexer.position();
    auto lastIndex = 0_z;
    auto res = false;

    _tokens.clear();
    _nodes.clear();
    _map.clear();
    _completions.clear();
    _completed.clear();

    // Avoid looking up the same rule multiple times in the prediction stage (see below).
    auto addedSym = std::vector<Symbol>();
    auto symAdded = std::vector<bool>(numSymbols);

    // Initial states.
    _nodes.emplace_back();
    for (auto k = ranges[startSymbol].begin; k < ranges[startSymbol].end; k++) _node(0, 0, sorted[k], 0);

    // Parse greedily, until there are no further possibilities.
    // Inv: `map` maps all `State`s of items to the items' addresses.
    for (auto i = 0_z; !_nodes[i].empty(); i++) {

      // "Prediction/completion" stage.
      for (auto j = 0_z; j < _nodes[i].size(); j++) {
        // Note that `std::deque::push_back()` invalidates iterators, but not references.
        // See: https://en.cppreference.com/w/cpp/container/deque/push_back
        auto& sref = _nodes[i][j];
        auto const& s = sref.state;
        auto const& [sl, sr] = rules[s.rule];
        if (s.progress < sr.size()) {
          // Perform prediction.
          auto const& [sym, prec] = sr[s.progress];
          if (!symAdded[sym]) {
            symAdded[sym] = true;
            addedSym.push_back(sym);
            for (auto k = ranges[sym].begin; k < ranges[sym].end; k++) _node(i, i, sorted[k], 0);
          }
          // Add to completion candidates.
          _completions.emplace(std::pair(i, sym), &sref);
          // Special null-completion (if `sym` is already null-completed, we are late, so we have to complete here).
          auto const& [begin, end] = _completed.equal_range(std::pair(i, sym));
          for (auto it = begin; it != end; it++) {
            auto& tref = *it->second;
            auto const& t = tref.state;
            auto const& [tl, tr] = rules[t.rule];
            assert(t.progress == tr.size() && tl.first == sym);
            if (prec <= tl.second) _transition(&sref, &tref, _node(s.begin, i, s.rule, s.progress + 1));
          }
        } else {
          // Perform completion.
          auto const& [sym, prec] = sl;
          auto const& [begin, end] = _completions.equal_range(std::pair(s.begin, sym));
          for (auto it = begin; it != end; it++) {
            auto& tref = *it->second;
            auto const& t = tref.state;
            auto const& [tl, tr] = rules[t.rule];
            assert(t.progress < tr.size() && tr[t.progress].first == sym);
            if (tr[t.progress].second <= prec) _transition(&tref, &sref, _node(t.begin, i, t.rule, t.progress + 1));
          }
          // If null, add to known null-completions.
          if (s.begin == i) _completed.emplace(std::pair(i, sym), &sref);
        }
      }
      // Clear flags.
      for (auto const sym: addedSym) symAdded[sym] = false;
      addedSym.clear();

      // Check if the start symbol completes and update result.
      auto found = false;
      for (auto& sref: _nodes[i]) {
        auto const& s = sref.state;
        auto const& [sl, sr] = rules[s.rule];
        if (sl.first == startSymbol && s.begin == 0 && s.progress == sr.size()) found = true;
      }
      if (found) {
        last = _lexer.position();
        lastIndex = i;
        res = true;
      }

      // Advance to next position.
      auto const& token = _nextToken();
      if (!token) break; // EOF.

      // "Scanning" stage.
      _tokens.push_back(*token);
      _nodes.emplace_back();
      _map.clear();
      auto const& [sym, prec] = std::pair(token->id, PrecedenceMax);
      for (auto& sref: _nodes[i]) {
        // Perform single-token shift.
        auto const& s = sref.state;
        auto const& [sl, sr] = rules[s.rule];
        if (s.progress < sr.size() && sr[s.progress].first == sym && sr[s.progress].second <= prec)
          _transition(&sref, &_tokens.back(), _node(s.begin, i + 1, s.rule, s.progress + 1));
      }
    }

    // Restore last valid position and return.
    _lexer.revert(last);
    _tokens.resize(lastIndex);
    _nodes.resize(lastIndex + 1);
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
  auto Parser::lastError(size_t begin, size_t end, std::optional<Symbol> const& got) const -> ParserError {
    assert(_nodes.size() == _tokens.size() + 1);
    auto pos = _tokens.size();
    auto expected = std::vector<Symbol>();
    for (auto const& node: mDP[pos]) {
      auto const& s = node.state;
      auto const& [lhs, rhs] = rules[s.rule];
      if (s.progress < rhs.size()) expected.push_back(rhs[s.progress].first);
    }
    std::sort(expected.begin(), expected.end());
    expected.resize(static_cast<size_t>(std::unique(expected.begin(), expected.end()) - expected.begin()));
    return {begin, end, expected, got};
  }
  */

}
