#include "parser.hpp"
#include <algorithm>
#include <iostream> // TEMP CODE
#include <unordered_set>

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

  auto GrammarBuilder::make() const -> Grammar {
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

  auto countNodes(std::vector<std::list<Node>> const& a) -> size_t {
    auto res = 0_z;
    for (auto const& curr: a) res += curr.size();
    return res;
  }

  auto countPrevs(std::vector<std::list<Node>> const& a) -> size_t {
    auto res = 0_z;
    for (auto const& curr: a)
      for (auto const& node: curr) res += node.prev.size();
    return res;
  }

  auto countNexts(std::vector<std::list<Node>> const& a) -> size_t {
    auto res = 0_z;
    for (auto const& curr: a)
      for (auto const& node: curr) res += node.next.size();
    return res;
  }

  auto Parser::advance() -> bool {
    if (_run()) {
      // Success.
      std::cout << "Before: ";
      std::cout << countNodes(_nodes) << " nodes, ";
      std::cout << countPrevs(_nodes) << " back links, ";
      std::cout << countNexts(_nodes) << " forward links." << std::endl;
      _prune();
      std::cout << "After: ";
      std::cout << countNodes(_nodes) << " nodes, ";
      std::cout << countPrevs(_nodes) << " back links, ";
      std::cout << countNexts(_nodes) << " forward links." << std::endl;
      return true;
    } else if (auto const token = _nextToken()) {
      // Failure.
      std::cout << "Parse error." << std::endl;
      return false;
    } else {
      // Reached EOF.
      return false;
    }
  }

  auto Parser::showState(Node const& node, std::vector<std::string> const& names) const -> std::string {
    auto const& rules = _grammar.rules;
    auto const& s = node.state;
    auto res = std::string();
    res += std::to_string(s.begin) + "-" + std::to_string(s.end) + ", ";
    res += names.at(rules[s.rule].lhs.first) + " ::=";
    for (auto i = 0_z; i < rules[s.rule].rhs.size(); i++) {
      if (i == s.progress) res += " |";
      res += " " + names.at(rules[s.rule].rhs[i].first);
    }
    if (s.progress == rules[s.rule].rhs.size()) res += " |";
    res += "\n";
    return res;
  }

  auto Parser::showStates(std::vector<std::string> const& names) const -> std::string {
    assert(_nodes.size() == _tokens.size() + 1);
    auto res = std::string();
    auto i = 0_z;
    for (auto const& token: _tokens) {
      res += "States at position " + std::to_string(i) + ":\n";
      for (auto const& node: _nodes[i]) res += showState(node, names);
      res += "\n";
      if (i < _tokens.size()) res += "Next token: " + names.at(token.id) + "\n";
      i++;
    }
    return res;
  }

  // Returns next non-ignored token, or `std::nullopt` if reaches EOF.
  auto Parser::_nextToken() -> std::optional<Token> {
    while (!_stream.eof()) {
      auto const token = _stream.advance();
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
    auto const& sorted = _grammar.sorted;
    auto const& ranges = _grammar.ranges;

    auto last = _stream.position();
    auto lastIndex = 0_z;
    auto res = false;

    _tokens.clear();
    _nodes.clear();
    _map.clear();
    _completions.clear();
    _completed.clear();

    // Initial states.
    _nodes.emplace_back();
    for (auto k = ranges[startSymbol].begin; k < ranges[startSymbol].end; k++) _node(0, 0, sorted[k], 0);

    // Parse greedily, until there are no further possibilities.
    // Inv: `map` maps all `State`s of items to the items' addresses.
    for (auto i = 0_z; !_nodes[i].empty(); i++) {

      // "Prediction/completion" stage.
      for (auto& sref: _nodes[i]) {
        // Note that `std::list::push_back()` will not invalidate iterators or references.
        // The past-the-end iterator remains past-the-end, so this loop will eventually cover newly-inserted items.
        // See: https://en.cppreference.com/w/cpp/container/list/push_back
        auto const& s = sref.state;
        auto const& [sl, sr] = rules[s.rule];
        if (s.progress < sr.size()) {
          // Perform prediction.
          auto const& [sym, prec] = sr[s.progress];
          for (auto k = ranges[sym].begin; k < ranges[sym].end; k++)
            if (prec <= rules[sorted[k]].lhs.second) _node(i, i, sorted[k], 0);
          // Add to completion candidates.
          _completions.emplace(std::pair(i, sym), &sref);
          // Special null-completion (if `sym` is already null-completed, we are late, so we have to complete here.)
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
          // If null, add to known null-completions (so that late predictions have a chance to catch up.)
          if (s.begin == i) _completed.emplace(std::pair(i, sym), &sref);
        }
      }

      // Check if the start symbol is completed and update result.
      for (auto& sref: _nodes[i]) {
        auto const& s = sref.state;
        auto const& [sl, sr] = rules[s.rule];
        assert(s.end == i);
        if (sl.first == startSymbol && s.begin == 0 && s.progress == sr.size()) {
          last = _stream.position();
          lastIndex = i;
          res = true;
          break;
        }
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
    _stream.revert(last);
    _tokens.resize(lastIndex);
    _nodes.resize(lastIndex + 1);
    return res;

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

  // Removes all nodes unreachable from the final states.
  auto Parser::_prune() -> void {
    assert(_nodes.size() == _tokens.size() + 1);
    auto const& rules = _grammar.rules;
    auto const& startSymbol = _grammar.startSymbol;
    auto const len = _tokens.size();
    auto stk = std::vector<Node const*>();
    auto v = std::unordered_set<Node const*>();

    // Start from the final states.
    for (auto& sref: _nodes[len]) {
      auto const& s = sref.state;
      auto const& [sl, sr] = rules[s.rule];
      assert(s.end == len);
      if (sl.first == startSymbol && s.begin == 0 && s.progress == sr.size()) {
        stk.push_back(&sref);
        v.insert(&sref);
      }
    }

    // Mark reachability from end, depth-first.
    while (!stk.empty()) {
      auto const& node = *stk.back();
      stk.pop_back();
      for (auto const& [prev, child]: node.prev) {
        // Previous node.
        if (!v.contains(prev)) {
          stk.push_back(prev);
          v.insert(prev);
        }
        // Child node (if applicable).
        if (auto const opt = std::get_if<Node*>(&child); opt) {
          if (!v.contains(*opt)) {
            stk.push_back(*opt);
            v.insert(*opt);
          }
        }
      }
    }

    // Remove unreachable nodes, as well as all edges pointing to them.
    for (auto& curr: _nodes) {
      for (auto it = curr.begin(); it != curr.end();) {
        auto& node = *it;
        if (!v.contains(&node)) {
          it = curr.erase(it);
          continue;
        }
        // Mid: `node` is reachable.
        // All nodes pointed by its `prev` links must also be reachable.
        for (auto itn = node.next.begin(); itn != node.next.end();) {
          auto& [next, _] = *itn;
          if (!v.contains(next)) {
            itn = node.next.erase(itn);
            continue;
          }
          // Mid: `next` is reachable.
          // The `_` (child node) must also be reachable.
          itn++;
        }
        it++;
      }
    }
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
