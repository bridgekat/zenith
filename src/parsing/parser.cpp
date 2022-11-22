#include "parser.hpp"
#include <algorithm>
#include <unordered_map>

namespace Parsing {

  auto operator==(EarleyParser::State const& a, EarleyParser::State const& b) -> bool {
    return a.startPos == b.startPos && a.rule == b.rule && a.progress == b.progress;
  }

  auto operator==(EarleyParser::Location const& a, EarleyParser::Location const& b) -> bool {
    return a.pos == b.pos && a.index == b.index;
  }

  // Parse greedily, until there are no further possibilities.
  // Parsing is considered successful only when the last position contains a completed root symbol.
  auto EarleyParser::nextSentence() -> bool {
    if (mDirty) {
      process();
      mDirty = false;
    }
    auto error = std::optional<ParserError>();
    while (true) {
      auto const& [found, nextToken] = run();
      if (found) {
        // Successful parse.
        if (mSentence.empty()) unimplemented;
        if (error) mErrors.push_back(*error);
        return true;
      }
      if (!nextToken) {
        // EOF.
        if (!mSentence.empty()) {
          // EOF with incomplete sentence.
          if (!error) error = lastError(mSentence.back().endPos, mSentence.back().endPos, std::nullopt);
          else error->endPos = mSentence.back().endPos;
        }
        if (error) mErrors.push_back(*error);
        return false;
      }
      // Mid: !index && nextToken
      // Error.
      if (!error) error = lastError(nextToken->startPos, nextToken->endPos, mPatterns.at(nextToken->pattern).sym.first);
      else error->endPos = nextToken->endPos;
      // Skip at least one token to avoid infinite loops.
      if (mSentence.empty()) {
        auto tok = mLexer.nextToken();
        while (tok && mPatterns.at(tok->pattern).sym.first == mIgnoredSymbol) tok = mLexer.nextToken();
      }
    }
  }

  auto EarleyParser::showState(LinkedState const& ls, std::vector<std::string> const& names) const -> std::string {
    auto const& [s, links] = ls;
    auto res = std::to_string(s.startPos) + ", <" + names.at(mRules[s.rule].lhs.first) + "> ::= ";
    for (auto i = 0_z; i < mRules[s.rule].rhs.size(); i++) {
      if (i == s.progress) res += "|";
      res += "<" + names.at(mRules[s.rule].rhs[i].first) + ">";
    }
    if (s.progress == mRules[s.rule].rhs.size()) res += "|";
    res += "\n";
    return res;
  }

  auto EarleyParser::showStates(std::vector<std::string> const& names) const -> std::string {
    if (mDP.size() != mSentence.size() + 1) unreachable;
    auto res = std::string();
    for (auto pos = 0_z; pos <= mSentence.size(); pos++) {
      res += "States at position " + std::to_string(pos) + ":\n";
      for (auto const& ls: mDP[pos]) res += showState(ls, names);
      res += "\n";
      if (pos < mSentence.size())
        res += "Next token: <" + names.at(mPatterns.at(mSentence[pos].pattern).sym.first) + ">\n";
    }
    return res;
  }

  // See: https://en.wikipedia.org/wiki/Earley_parser#The_algorithm for an overview.
  // See: https://loup-vaillant.fr/tutorials/earley-parsing/ for a possible way to deal with empty rules.
  // Other related information:
  //   https://github.com/jeffreykegler/kollos/blob/master/notes/misc/leo2.md
  //   https://jeffreykegler.github.io/Marpa-web-site/
  //   https://arxiv.org/pdf/1910.08129.pdf
  auto EarleyParser::process() -> void {
    // Find the number of symbols involved.
    mNumSymbols = mStartSymbol + 1;
    for (auto const& [lhs, rhs]: mRules) {
      mNumSymbols = std::max(mNumSymbols, lhs.first + 1);
      for (auto const& r: rhs) mNumSymbols = std::max(mNumSymbols, r.first + 1);
    }

    // Find all empty rules, and confirm that no other rules are nullable.
    // It is quite possible to support arbitrary nullable rules, but that would make things significantly messier
    // (just think about ambiguous empty derivations...)
    mEmptyRule = std::vector<std::optional<size_t>>(mNumSymbols);
    for (auto i = 0_z; i < mRules.size(); i++) {
      auto const& [lhs, rhs] = mRules[i];
      if (rhs.empty()) mEmptyRule[lhs.first] = i;
    }
    for (auto i = 0_z; i < mRules.size(); i++) {
      auto const& [lhs, rhs] = mRules[i];
      if (mEmptyRule[lhs.first] != i) {
        bool f = false;
        for (auto const& r: rhs)
          if (!mEmptyRule[r.first]) f = true;
        if (!f) unimplemented;
      }
    }

    // Sort all non-empty (non-nullable) rules by symbol ID (for faster access in `run()`).
    // Also accumulate the lengths of RHS (plus one) of the production rules (for better hashing in `run()`).
    mSorted.clear();
    mTotalLength.clear();
    mTotalLength.push_back(0);
    for (auto i = 0_z; i < mRules.size(); i++) {
      auto const& [lhs, rhs] = mRules[i];
      if (mEmptyRule[lhs.first] != i) mSorted.push_back(i);
      mTotalLength.push_back(mTotalLength[i] + rhs.size() + 1);
    }
    std::sort(mSorted.begin(), mSorted.end(), [this](size_t i, size_t j) { return mRules[i].lhs < mRules[j].lhs; });
    auto n = mSorted.size();

    // For each symbol find the index of its first production rule
    // (for faster access in `run()`, if none then set to `n`.)
    mFirstRule = std::vector<size_t>(mNumSymbols, n);
    for (auto i = 0_z; i < n; i++) {
      auto const& [lhs, rhs] = mRules[mSorted[i]];
      if (mFirstRule[lhs.first] == n) mFirstRule[lhs.first] = i;
    }
  }

  // Pre: `mNumSymbols`, `mEmptyRule`, `mSorted`, `mFirstRule` and `mTotalLength` must be consistent with current rules.
  // Post: `mSentence` and `mDP` contains the parsing result.
  // Returns { index, nextToken }.
  auto EarleyParser::run() -> std::pair<bool, std::optional<Token>> {
    if (!mStartSymbol) unimplemented;
    mSentence.clear();
    mDP.clear();

    // Minor optimization: avoid looking up rules multiple times (see below).
    auto added = std::vector<Symbol>();
    auto isAdded = std::vector<bool>(mNumSymbols);

    // A hash function for DP states, for mapping states back to indices.
    auto hash = [this](State const& x) { return x.startPos * 524287u + (mTotalLength[x.rule] + x.progress); };
    auto map = std::unordered_map<State, size_t, decltype(hash)>(0, hash);

    // Initial states.
    mDP.emplace_back();
    for (auto i = mFirstRule[mStartSymbol]; i < mSorted.size() && mRules[mSorted[i]].lhs.first == mStartSymbol; i++) {
      auto s = State{0, mSorted[i], 0};
      map[s] = mDP[0].size();
      mDP[0].push_back(LinkedState{s, {}});
    }
    auto nextToken = std::optional<Token>();

    // Invariant: `map` maps all `state`s of items of `mDP[pos]` to the items' indices.
    for (auto pos = 0_z;; pos++) {

#define ensure(s)                           \
  if (!map.contains(s)) {                   \
    map[s] = mDP[pos].size();               \
    mDP[pos].push_back(LinkedState{s, {}}); \
  }

      // "Prediction/completion" stage.
      for (auto i = 0_z; i < mDP[pos].size(); i++) {
        auto s = mDP[pos][i].state;
        auto const& [lhs, rhs] = mRules[s.rule];
        if (s.progress < rhs.size()) {
          // Perform prediction.
          auto const& [sym, prec] = rhs[s.progress];
          if (!isAdded[sym]) {
            isAdded[sym] = true;
            added.push_back(sym);
            for (auto j = mFirstRule[sym]; j < mSorted.size() && mRules[mSorted[j]].lhs.first == sym; j++) {
              auto u = State{pos, mSorted[j], 0};
              ensure(u);
            }
          }
          // Perform empty completion (if `sym` is nullable, we could skip it).
          if (mEmptyRule[sym] && prec <= mRules[*mEmptyRule[sym]].lhs.second) {
            auto t = State{pos, *mEmptyRule[sym], 0};
            auto u = State{s.startPos, s.rule, s.progress + 1};
            ensure(t);
            ensure(u);
            mDP[pos][map[u]].links.push_back({
              {pos,      i},
              {pos, map[t]}
            });
          }
        } else {
          // Perform nonempty completion.
          auto tpos = s.startPos;
          if (tpos == pos) continue;
          auto const& [sym, prec] = lhs;
          for (auto j = 0_z; j < mDP[tpos].size(); j++) {
            auto t = mDP[tpos][j].state;
            auto const& trhs = mRules[t.rule].rhs;
            if (t.progress < trhs.size() && trhs[t.progress].first == sym && trhs[t.progress].second <= prec) {
              auto u = State{t.startPos, t.rule, t.progress + 1};
              ensure(u);
              mDP[pos][map[u]].links.push_back({
                {tpos, j},
                { pos, i}
              });
            }
          }
        }
      }
      // Clear flags.
      for (auto sym: added) isAdded[sym] = false;
      added.clear();

#undef ensure

      // Advance to next position.
      auto restore = mLexer.position();
      nextToken = mLexer.nextToken();
      while (nextToken && mPatterns.at(nextToken->pattern).sym.first == mIgnoredSymbol) nextToken = mLexer.nextToken();
      if (!nextToken) break; // EOF.
      mSentence.push_back(*nextToken);

      // "Scanning" stage.
      // Also updating `map` to reflect `states[pos + 1]` instead (re-establish loop invariant).
      mDP.emplace_back();
      map.clear();
      auto const& [sym, prec] = mPatterns.at(nextToken->pattern).sym;
      for (auto i = 0_z; i < mDP[pos].size(); i++) {
        auto s = mDP[pos][i].state;
        auto const& rhs = mRules[s.rule].rhs;
        if (s.progress < rhs.size() && rhs[s.progress].first == sym && rhs[s.progress].second <= prec) {
          auto u = State{s.startPos, s.rule, s.progress + 1};
          // No need to check for presence! `s` is already unique.
          map[u] = mDP[pos + 1].size();
          mDP[pos + 1].push_back(LinkedState{u, {{{pos, i}, Leaf}}});
        }
      }

      // If no more possibilities then restore and stop.
      if (mDP[pos + 1].empty()) {
        mLexer.setPosition(restore);
        mSentence.pop_back();
        mDP.pop_back();
        break;
      }
    }

    // Check if the start symbol completes.
    if (mDP.size() != mSentence.size() + 1) unreachable;
    auto pos = mSentence.size();
    auto found = false;
    for (auto i = 0_z; i < mDP[pos].size(); i++) {
      auto s = mDP[pos][i].state;
      auto const& [lhs, rhs] = mRules[s.rule];
      if (lhs.first == mStartSymbol && s.startPos == 0 && s.progress == rhs.size()) found = true;
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
     *   Number of states (i.e. `mDP[pos].size()`) = O(|G|n)
     *   Prediction = O(|G|n) (iterating through states = O(|G|n), total states added = O(|G|))
     *   Completion = O(|G|²n²) (iterating though states = O(|G|n), time for each state = O(|G|n))
     *              = O(|G|n) for unambiguous (iterating through states = O(|G|n), total states added = O(|G|n))
     *   Scanning   = O(|G|n) (iterating through states = O(|G|n))
     * Overall: O(|G|²n³)
     *          O(|G|n²) for unambiguous (*)
     */

    return {found, nextToken};
  }

  // For use in `nextSentence()` only
  auto EarleyParser::lastError(size_t startPos, size_t endPos, std::optional<Symbol> const& got) const -> ParserError {
    if (mDP.size() != mSentence.size() + 1) unreachable;
    auto pos = mSentence.size();
    auto expected = std::vector<Symbol>();
    for (auto const& ls: mDP[pos]) {
      auto const& s = ls.state;
      auto const& [lhs, rhs] = mRules[s.rule];
      if (s.progress < rhs.size()) expected.push_back(rhs[s.progress].first);
    }
    std::sort(expected.begin(), expected.end());
    expected.resize(static_cast<size_t>(std::unique(expected.begin(), expected.end()) - expected.begin()));
    return {startPos, endPos, expected, got};
  }

}
