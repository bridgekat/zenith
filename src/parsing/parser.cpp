#include "parser.hpp"
#include <algorithm>

namespace apimu::parsing {
#include "macros_open.hpp"

  auto GrammarBuilder::start(Symbol value) -> GrammarBuilder& {
    _startSymbol = value;
    return *this;
  }
  auto GrammarBuilder::ignored(Symbol value) -> GrammarBuilder& {
    _ignoredSymbol = value;
    return *this;
  }
  auto GrammarBuilder::rule(InputPair lhs, std::vector<InputPair> const& rhs) -> GrammarBuilder& {
    auto& rule = _rules.emplace_back();
    rule.lhs = lhs.value;
    for (auto& r: rhs) rule.rhs.push_back(r.value);
    return *this;
  }

  auto GrammarBuilder::makeGrammar() const -> Grammar {
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

    // Sort all rules by LHS symbol ID and precedence (for faster access).
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

  // Returns next non-ignored token, or `std::nullopt` if reaches EOF.
  auto EarleyParser::_nextToken() -> std::optional<Token> {
    while (auto const token = _marked.next())
      if (token->id != _grammar.ignoredSymbol) return token;
    return {};
  }

  // Skip `count` tokens.
  auto EarleyParser::_skipTokens(size_t count) -> void {
    for (auto i = 0_z; i < count; i++) _nextToken();
  }

  // Adds a node with state `state` to `_nodes` while registering it in `_map`.
  // If a node with the given state is already added, returns a pointer to it.
  auto EarleyParser::_node(size_t begin, size_t end, size_t rule, size_t progress) -> size_t {
    assert(_ranges.size() == end + 1);
    auto const state = Node::State{begin, end, rule, progress};
    if (auto const it = _map.find(state); it != _map.end()) return it->second;
    _nodes.push_back(Node{state, {}, {}});
    _ranges[end].end = _nodes.size();
    return _map[state] = _nodes.size() - 1;
  }

  // Adds a transition from `prev` to `next` which goes through `child`.
  // This adds backward links only. Forward links are deferred to the disambiguation stage.
  auto EarleyParser::_transition(size_t prev, bool leaf, size_t child, size_t next) -> void {
    _nodes[next].prev.push_back(Node::Link{prev, leaf, child});
  }

  // Parse greedily, until reached designated length or there are no further possibilities.
  // Pre:
  // - `_ranges.size() == _tokens.size() + 1`;
  // - `_map` maps all `State`s of nodes to the nodes' indices;
  // - `_completions` contains all completion candidate nodes' indices;
  // - `_completed` contains all null-completed nodes' indices.
  auto EarleyParser::_run(bool recoveryMode, std::optional<size_t> optLength) -> Result {
    assert(_marked.position() == _tokens.size());
    assert(_ranges.size() == _tokens.size() + 1);
    auto const length = optLength ? *optLength : std::numeric_limits<size_t>::max();
    auto const& rules = _grammar.rules;
    auto const& sorted = _grammar.sorted;
    auto const& offset = _tokens.size();

    for (auto i = offset; i - offset < length; i++) {
      // Unconditional null-completion mode for error recovery.
      auto const unconditional = (i == offset && recoveryMode);

      // "Prediction/completion" stage.
      for (auto si = _ranges[i].begin; si < _ranges[i].end; si++) {
        auto const s = _nodes[si].state;
        auto const& [sl, sr] = rules[s.rule];
        if (s.progress < sr.size()) {
          // Perform prediction.
          auto const& [sym, prec] = sr[s.progress];
          for (auto k = _grammar.ranges[sym].begin; k < _grammar.ranges[sym].end; k++)
            if (prec <= rules[sorted[k]].lhs.second) _node(i, i, sorted[k], 0);
          // Add to completion candidates.
          _completions.emplace(std::pair(i, sym), si);
          // Special null-completion (if `sym` is already null-completed, we are late, so we have to complete here.)
          auto const& [begin, end] = _completed.equal_range(std::pair(i, sym));
          for (auto it = begin; it != end; it++) {
            auto const ti = it->second;
            auto const t = _nodes[ti].state;
            auto const& [tl, tr] = rules[t.rule];
            assert(t.progress == tr.size() && tl.first == sym);
            if (prec <= tl.second) _transition(si, false, ti, _node(s.begin, i, s.rule, s.progress + 1));
          }
          // Unconditional null-completion.
          if (unconditional) _node(s.begin, i, s.rule, s.progress + 1);
        } else {
          // Perform completion.
          auto const& [sym, prec] = sl;
          auto const& [begin, end] = _completions.equal_range(std::pair(s.begin, sym));
          for (auto it = begin; it != end; it++) {
            auto const ti = it->second;
            auto const t = _nodes[ti].state;
            auto const& [tl, tr] = rules[t.rule];
            assert(t.progress < tr.size() && tr[t.progress].first == sym);
            if (tr[t.progress].second <= prec) _transition(ti, false, si, _node(t.begin, i, t.rule, t.progress + 1));
          }
          // If null, add to known null-completions (so that late predictions have a chance to catch up.)
          if (s.begin == i) _completed.emplace(std::pair(i, sym), si);
        }
      }

      // Advance to next position.
      auto const& opt = _nextToken();
      if (!opt) return finalStates().empty() ? Result::eofFailure : Result::eofSuccess;
      _marked.mark();
      _tokens.push_back(*opt);
      _ranges.push_back(IndexRange{_nodes.size(), _nodes.size()});

      // "Scanning" stage.
      auto const& ti = _tokens.size() - 1;
      auto const& [sym, prec] = std::pair(_tokens[ti].id, PrecedenceMax);
      for (auto si = _ranges[i].begin; si < _ranges[i].end; si++) {
        // Perform single-token shift.
        auto const s = _nodes[si].state;
        auto const& [sl, sr] = rules[s.rule];
        if (s.progress < sr.size() && sr[s.progress].first == sym && sr[s.progress].second <= prec)
          _transition(si, true, ti, _node(s.begin, i + 1, s.rule, s.progress + 1));
      }

      // Check if any new state is created.
      if (_ranges[i + 1].begin == _ranges[i + 1].end) return Result::emptyFailure;
    }

    // Reached designated length.
    return Result::reachedLength;

    /*
     * ===== A hand-wavey argument for correctness =====
     * By induction prove (1):
     *     If a (possibly empty) substring has a derivation tree, and the root node of the tree was predicted in the
     *     "prediction/completion" stage at the `begin` position of the substring, then the root node of that tree will
     *     eventually get completed, no later than the "prediction/completion" stage performed at the `end` position of
     *     the substring.
     * - Base cases (trivial RHS):
     *   - If tree contains a single token: such item will always be completed in the "scanning" stage.
     *   - If tree is empty (RHS of root derivation has length 0): such item will always be completed once predicted.
     * - Induction step (non-trivial RHS):
     *   By induction prove (2):
     *       Every prefix of the root production rule will be reached, no later than the "prediction/completion" stage
     *       performed at the corresponding positions.
     *   - Base case (empty prefix): initially true.
     *   - Induction step (nonempty prefix): if last symbol of the prefix is...
     *     - Terminal: by IH of (2) + "scanning" stage.
     *     - Nonempty nonterminal: by IH of (2), the prefix minus the last symbol will be reached; then all possible
     *       rules for the last symbol will be predicted at the last position, with the root item being added to
     *       `_completions`. Now by IH of (1), the correct rules for the symbol will get completed (in a strictly later
     *       position, so their completions must happen after the aforementioned prediction), and the root item will
     *       have its `progress` incremented by 1.
     *     - Empty nonterminal: similarly by IH of (2).
     *       - If completion happens after prediction, same as above;
     *       - Otherwise, item is added to `_completed` before the current prediction, and will be found immediately by
     *         the "special null-completion" code, which also advances the root item's progress by 1.
     *
     * ===== A hand-wavey argument for time complexity =====
     * Number of states on each position `forest[pos].size()` = O(|G|n).
     * If grammar is unambiguous, each state can have at most 1 back link. Otherwise, following 2 links will give 2
     * different but valid parse trees.
     *
     * For each iteration of the outer loop:
     * - Prediction = O(|G|²n) (iterating through states = O(|G|n), time for each state = O(|G|)).
     * - Completion = O(|G|²n²) (iterating though states = O(|G|n), time for each state = O(|G|n)).
     *              = O(|G|n) for unambiguous cases (iterating through states = O(|G|n), total links added = O(|G|n)).
     * - Scanning   = O(|G|n) (iterating through states = O(|G|n)).
     *
     * Overall: O(|G|²n³) for all cases;
     *          O(|G|²n²) for unambiguous cases.
     */
  }

  // Restores parser state to given index.
  // This does not remove any forward links (since we assume that none has been created yet).
  // Also does not remove any backward links (since they never point forwards).
  auto EarleyParser::_restore(size_t i) -> void {
    assert(_marked.position() == _tokens.size());
    assert(_ranges.size() == _tokens.size() + 1);
    assert(i <= _tokens.size());

    _marked.revert(i);
    _tokens.resize(i);
    _nodes.resize(_ranges[i].end);
    _ranges.resize(i + 1);

    auto map = decltype(_map)();
    for (auto const& item: _map)
      if (item.second < _nodes.size()) map.insert(item);
    _map = std::move(map);

    auto completions = decltype(_completions)();
    for (auto const& item: _completions)
      if (item.second < _nodes.size()) completions.insert(item);
    _completions = std::move(completions);

    auto completed = decltype(_completed)();
    for (auto const& item: _completed)
      if (item.second < _nodes.size()) completed.insert(item);
    _completed = std::move(completed);
  }

  // Returns a list of final states at given position (if any).
  auto EarleyParser::finalStates(std::optional<size_t> optPosition) const -> std::vector<size_t> {
    assert(_tokens.size() + 1 == _ranges.size());
    assert(!optPosition || *optPosition <= _tokens.size());
    auto const i = optPosition ? *optPosition : _tokens.size();
    auto const& rules = _grammar.rules;
    auto const& startSymbol = _grammar.startSymbol;

    // Check if the start symbol is completed at position `i`.
    auto res = std::vector<size_t>();
    for (auto si = _ranges[i].begin; si < _ranges[i].end; si++) {
      auto const& s = _nodes[si].state;
      auto const& [sl, sr] = rules[s.rule];
      if (sl.first == startSymbol && s.begin == 0 && s.progress == sr.size()) res.push_back(si);
    }
    return res;
  }

  auto EarleyParser::parse() -> bool {
    // Start clean.
    _marked.clear();
    _tokens.clear();
    _nodes.clear();
    _ranges.clear();
    _map.clear();
    _completions.clear();
    _completed.clear();

    // Initial states.
    _ranges.push_back(IndexRange{0, 0});
    for (auto k = _grammar.ranges[_grammar.startSymbol].begin; k < _grammar.ranges[_grammar.startSymbol].end; k++)
      _node(0, 0, _grammar.sorted[k], 0);

    // Main loop.
    auto errors = false;
    auto recoveryMode = false;
    while (true) {
      auto result = _run(recoveryMode);

      // If success, return.
      if (result == Result::eofSuccess) return !errors;
      // Try rolling back.
      if (_params.rollback)
        for (auto i = _tokens.size(); i-- > 1;)
          if (!finalStates(i).empty()) {
            _restore(i);
            return !errors;
          }

      // Enter error recovery mode.
      assert(result == Result::eofFailure || result == Result::emptyFailure);
      errors = true;
      recoveryMode = true;

      // Generate an error and call handler.
      auto expected = std::vector<Symbol>();
      auto got = std::optional<Token>();
      auto const& [begin, end] = _ranges[_ranges.size() - (result == Result::emptyFailure ? 2 : 1)];
      for (auto si = begin; si < end; si++) {
        auto const& s = _nodes[si].state;
        auto const& [sl, sr] = _grammar.rules[s.rule];
        if (s.progress < sr.size()) expected.push_back(sr[s.progress].first);
      }
      std::sort(expected.begin(), expected.end());
      expected.resize(static_cast<size_t>(std::unique(expected.begin(), expected.end()) - expected.begin()));
      if (result == Result::emptyFailure) got = _tokens.back();
      _handler.parsingError(std::move(expected), std::move(got));

      // If reached EOF, return.
      if (result == Result::eofFailure) return false;

      // Perform error recovery (try advancing rules & skipping tokens...)
      auto success = false;
      auto position = _tokens.size();
      for (auto skipped = 0_z; skipped <= _params.maxSkipped; skipped++) {
        for (auto left = 0_z; left <= skipped; left++) {
          if (position < left) continue;
          // Multiple `MarkedStream`s will modify the same underlying token stream here...
          // But it should still be safe (net effect = advances the underlying token stream, by "TRUST ME").
          auto copy = *this;
          copy._restore(position - left);
          copy._skipTokens(skipped); // (1) Skipped more tokens than reverted.
          // Try parse.
          // (2) `_run()` only advances the underlying token stream.
          if (copy._run(true, _params.threshold) == Result::reachedLength) {
            _restore(position - left);
            _skipTokens(skipped);
            success = true;
          }
          if (success) break;
        }
        if (success) break;
      }

      // If recovery failed, return.
      if (!success) return false;
    }
  }

  auto EarleyParser::propagate(std::vector<size_t> stk) -> size_t {
    assert(_tokens.size() + 1 == _ranges.size());
    assert(!stk.empty());

    // Confirm that all given nodes refer to the same rule, and all are fully completed.
    auto const& r = _nodes[stk.back()].state;
    for (auto const curr: stk) {
      auto const& s = _nodes[curr].state;
      assert(s.begin == r.begin && s.end == r.end && s.rule == r.rule && s.progress == r.progress);
      assert(s.progress == _grammar.rules[s.rule].rhs.size());
    }

    // Find source node.
    auto res = stk.back();
    while (!_nodes[res].prev.empty()) res = _nodes[res].prev[0].sibling;
    assert(_nodes[res].state.progress == 0);

    // Mark reachability from sink nodes, depth-first.
    while (!stk.empty()) {
      auto const curr = stk.back();
      stk.pop_back();
      if (_nodes[curr].prev.empty()) assert(curr == res);
      auto const& s = _nodes[curr].state;
      for (auto const& [prev, leaf, child]: _nodes[curr].prev) {
        auto const& t = _nodes[prev].state;
        assert(t.begin == s.begin && t.end <= s.end && t.rule == s.rule && t.progress + 1 == s.progress);
        if (_nodes[prev].next.empty()) stk.push_back(prev); // First time becoming reachable, propagate on.
        _nodes[prev].next.push_back(Node::Link{curr, leaf, child});
      }
    }

    // Return source node.
    return res;
  }

  auto EarleyParser::unpropagate(std::vector<size_t> stk) -> void {
    while (!stk.empty()) {
      auto const curr = stk.back();
      stk.pop_back();
      for (auto const& [prev, leaf, child]: _nodes[curr].prev)
        if (!_nodes[prev].next.empty()) { // Forward links not yet cleared.
          stk.push_back(prev);
          _nodes[prev].next.clear();
        }
    }
  }

#include "macros_close.hpp"
}
