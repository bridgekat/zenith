#include <utility>
#include <optional>
#include <algorithm>
#include <unordered_map>
#include <core/base.hpp>
#include "parser.hpp"


namespace Parsing {

  using std::unordered_map;
  using std::optional, std::make_optional, std::nullopt;
  using std::variant, std::monostate;
  using std::holds_alternative, std::get, std::visit;


  ParseTree* EarleyParser::parse(const vector<Token>& str, Core::Allocator<ParseTree>& pool) {
    this->str = str;
    run();
    return getParseTree(pool);
  }

  size_t EarleyParser::toCharsStart(size_t pos) const noexcept {
    if (pos >= str.size()) return str.empty()? 0 : str.back().endPos;
    return str[pos].startPos;
  }

  size_t EarleyParser::toCharsEnd(size_t pos) const noexcept {
    if (pos >= str.size()) return str.empty()? 0 : str.back().endPos;
    return str[pos].endPos;
  }

  // For use in `run()` only
  void EarleyParser::logError(size_t pos) {
    if (dpa.size() != str.size() + 1 || pos >= dpa.size()) throw Core::Unreachable();

    vector<Symbol> expected;
    for (const LinkedState& ls: dpa[pos]) {
      const State& s = ls.state;
      const Rule& rule = rules[s.ruleIndex];
      if (s.rulePos < rule.rhs.size()) expected.push_back(rule.rhs[s.rulePos]);
    }
    size_t len = std::unique(expected.begin(), expected.end()) - expected.begin();
    expected.resize(len);

    optional<Symbol> got = pos < str.size() ? make_optional(str[pos].id) : nullopt;
    errors.emplace_back(toCharsStart(pos), toCharsEnd(pos), expected, got);
  }

  // See: https://en.wikipedia.org/wiki/Earley_parser#The_algorithm (for an overview)
  // See: https://loup-vaillant.fr/tutorials/earley-parsing/ (for a simple way to deal with ε rules)
  // Other related information:
  //   https://github.com/jeffreykegler/kollos/blob/master/notes/misc/leo2.md
  //   https://jeffreykegler.github.io/Marpa-web-site/
  //   https://arxiv.org/pdf/1910.08129.pdf
  // (I am not going to dig too deep into the theories about different parsing algorithms now!)

  void EarleyParser::run() {
    const size_t n = str.size(), m = rules.size();

    // Find the number `k` of symbols involved
    Symbol k = startSymbol + 1;
    for (const auto& [lhs, rhs]: rules) {
      k = std::max(k, lhs + 1);
      for (Symbol sym: rhs) k = std::max(k, sym + 1);
    }

    // Work out "nullable" nonterminals and their nullable rules (O(|G|²))
    // Currently we don't care about ambiguous nullables!
    nullable.clear();
    nullable.resize(k);
    bool updates = false;
    do {
      updates = false;
      for (size_t i = 0; i < m; i++) {
        Symbol lhs = rules[i].lhs;
        const auto& rhs = rules[i].rhs;
        if (!nullable[lhs].has_value()) {
          bool f = true;
          for (Symbol sym: rhs) {
            if (!nullable[sym].has_value()) { f = false; break; }
          }
          if (f) {
            nullable[lhs] = i;
            updates = true;
          }
        }
      }
    } while (updates);

    // Sort all rules by nonterminal id (for faster access)
    vector<size_t> sorted;
    for (size_t i = 0; i < m; i++) sorted.push_back(i);
    std::sort(sorted.begin(), sorted.end(), [this] (size_t a, size_t b) { return rules[a].lhs < rules[b].lhs; });

    // For each nonterminal find the id of its first production rule (for faster access, if none then set to `m`)
    // Also accumulate the lengths of RHS (plus one) of the production rules (for better hashing)
    vector<size_t> firstRule(k, m);
    vector<size_t> totalLength(m, 0);
    for (size_t i = 0; i < m; i++) {
      const auto& [lhs, rhs] = rules[sorted[i]];
      if (firstRule[lhs] == m) firstRule[lhs] = i;
      if (i + 1 < m) totalLength[i + 1] = totalLength[i] + rhs.size() + 1;
    }

    // The main DP array
    dpa.clear();
    dpa.resize(n + 1);

    // A hash function for DP states
    auto hash = [&totalLength] (const State& x) {
      return x.startPos * 524287u + (totalLength[x.ruleIndex] + x.rulePos);
    };
    unordered_map<State, size_t, decltype(hash)> mp(0, hash);

    // A minor optimization: avoid looking up rules multiple times (see below)
    vector<Symbol> added;
    vector<bool> isAdded(k);

    // Initial states
    for (size_t i = firstRule[startSymbol]; i < m && rules[sorted[i]].lhs == startSymbol; i++) {
      State s{ 0, sorted[i], 0 };
      mp[s] = dpa[0].size();
      dpa[0].emplace_back(s, nullopt, monostate{}, false);
    }

    // Invariant: `mp` maps all elements of `states[pos]` to their indices
    for (size_t pos = 0; pos <= n; pos++) {

      // "Prediction/completion" stage
      for (size_t i = 0; i < dpa[pos].size(); i++) {
        State s = dpa[pos][i].state;
        const auto& derived = rules[s.ruleIndex].rhs;
        if (s.rulePos < derived.size()) {
          // Perform prediction
          Symbol sym = derived[s.rulePos];
          // Avoid looking up rules multiple times...
          if (!isAdded[sym]) {
            isAdded[sym] = true;
            added.push_back(sym);
            // Add all rules for `sym`
            for (size_t j = firstRule[sym]; j < m && rules[sorted[j]].lhs == sym; j++) {
              State ss{ pos, sorted[j], 0 };
              if (!mp.contains(ss)) {
                mp[ss] = dpa[pos].size();
                dpa[pos].emplace_back(ss, nullopt, monostate{}, false);
              }
            }
          }
          // If `sym` is nullable, we could skip it (empty completion)
          if (nullable[sym].has_value()) {
            State ss{ s.startPos, s.ruleIndex, s.rulePos + 1 };
            if (!mp.contains(ss)) {
              mp[ss] = dpa[pos].size();
              dpa[pos].emplace_back(ss, Location{ pos, i }, EmptyChild{}, false);
            } else {
              // Ambiguity detected
              LinkedState& ls = dpa[pos][mp[ss]];
              ls.ambiguous = true;
              // TODO: prefer child with production rule of smaller index
            }
          }
        } else {
          // Perform nonempty completion
          if (derived.empty()) continue;
          Symbol lhs = rules[s.ruleIndex].lhs;
          // (TODO: optimize this loop for better time complexity bounds on unambiguous grammars?)
          // (Or maybe too many heap allocations will make it slower in practice?)
          for (size_t j = 0; j < dpa[s.startPos].size(); j++) {
            State t = dpa[s.startPos][j].state;
            const auto& tderived = rules[t.ruleIndex].rhs;
            if (t.rulePos < tderived.size() && tderived[t.rulePos] == lhs) {
              State tt{ t.startPos, t.ruleIndex, t.rulePos + 1 };
              if (!mp.contains(tt)) {
                mp[tt] = dpa[pos].size();
                dpa[pos].emplace_back(tt, Location{ s.startPos, j }, Location{ pos, i }, false);
              } else {
                // Ambiguity detected
                LinkedState& ls = dpa[pos][mp[tt]];
                ls.ambiguous = true;
                // TODO: prefer child with production rule of smaller index
              }
            }
          }
        }
      }
      // Clear flags
      for (Symbol sym: added) isAdded[sym] = false;
      added.clear();

      if (pos >= str.size()) break;
      Token tok = str[pos];

      // "Scanning" stage
      // Also updating `mp` to reflect `states[pos + 1]` instead
      mp.clear();
      for (size_t i = 0; i < dpa[pos].size(); i++) {
        State s = dpa[pos][i].state;
        const auto& derived = rules[s.ruleIndex].rhs;
        if (s.rulePos < derived.size() && derived[s.rulePos] == tok.id) {
          State ss{ s.startPos, s.ruleIndex, s.rulePos + 1 };
          // No need to check presence! `s` is already unique.
          mp[ss] = dpa[pos + 1].size();
          dpa[pos + 1].emplace_back(ss, Location{ pos, i }, tok, false);
        }
      }

      // Simple error recovery (TODO: limit total number of errors?)
      if (dpa[pos + 1].empty()) {
        // To minimise ambiguity, we don't add multiple states with the same rule-index.
        // This may be undesirable for rules with multiple error-symbols, but we keep it simple for now!
        vector<bool> f(m, false);
        for (size_t posj = pos + 1; posj --> 0;) { // [0, pos] decreasing, inclusive
          for (size_t j = 0; j < dpa[posj].size(); j++) {
            const State& s = dpa[posj][j].state;
            const auto& derived = rules[s.ruleIndex].rhs;
            if (s.rulePos < derived.size() && derived[s.rulePos] == errorSymbol && !f[s.ruleIndex]) {
              f[s.ruleIndex] = true;
              State ss{ s.startPos, s.ruleIndex, s.rulePos + 1 };
              // No need to check presence! `s.ruleIndex` is already unique.
              mp[ss] = dpa[pos + 1].size();
              dpa[pos + 1].emplace_back(ss, Location{ posj, j }, ErrorChild{}, false);
            }
          }
        }
        logError(pos);
      }

    }

    // Check if the start symbol completes at the end position
    fin = nullopt;
    for (size_t i = 0; i < dpa[n].size(); i++) {
      const State& s = dpa[n][i].state;
      const Rule& rule = rules[s.ruleIndex];
      if (s.startPos == 0 && rule.lhs == startSymbol && s.rulePos == rule.rhs.size()) {
        fin = { n, i };
        break;
      }
    }
    if (!fin) logError(n);

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
    *       - nullable nonterminal: by IH (2) + skipping at the "prediction/completion" stage.
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
  }

  // See: https://en.cppreference.com/w/cpp/utility/variant/visit
  template<class... Ts> struct Matcher: Ts... { using Ts::operator()...; };

  #define assert(expr) if (!(expr)) throw Core::Unreachable()

  // Constructs an empty parse tree for a nullable symbol.
  ParseTree* EarleyParser::nullParseTree(size_t pos, Symbol id, Core::Allocator<ParseTree>& pool) const {

    // Must be a nullable symbol
    assert(nullable[id].has_value());
    size_t ruleIndex = nullable[id].value();

    // Current node
    ParseTree* res = pool.pushBack(ParseTree{
      nullptr, nullptr,
      id,
      nullopt, ruleIndex,
      toCharsStart(pos), toCharsStart(pos)
    });

    // Link together
    ParseTree** last = &res->c;
    for (Symbol sym: rules[ruleIndex].rhs) {
      ParseTree* child = nullParseTree(pos, sym, pool);
      *last = child;
      last = &child->s;
    }

    return res;
  }

  // Constructs a parse tree that represents a parsing error.
  ParseTree* EarleyParser::errorParseTree(size_t startPos, size_t endPos, Core::Allocator<ParseTree>& pool) const {
    assert(errorSymbol.has_value());
    assert(endPos > 0);
    return pool.pushBack(ParseTree{
      nullptr, nullptr,
      *errorSymbol,
      nullopt, nullopt,
      toCharsStart(startPos), toCharsEnd(endPos - 1)
    });
  }

  // Constructs a parse tree for a completed DP state.
  ParseTree* EarleyParser::getParseTree(Location loc, Core::Allocator<ParseTree>& pool) const {
    const LinkedState* curr = &dpa[loc.pos][loc.i];
    const Rule& rule = rules[curr->state.ruleIndex];

    // Must be a completed state
    assert(curr->state.rulePos == rule.rhs.size());

    // Current node
    ParseTree* res = pool.pushBack(ParseTree{
      nullptr, nullptr,
      rule.lhs,
      nullopt, curr->state.ruleIndex,
      toCharsStart(curr->state.startPos), (loc.pos == 0 ? toCharsStart(loc.pos) : toCharsEnd(loc.pos - 1))
    });

    // Follow links to construct a list of children (in reverse order)
    vector<ParseTree*> children;
    for (size_t i = rule.rhs.size(); i --> 0;) {
      assert(curr->prev.has_value());

      ParseTree* child = visit(Matcher{
        [&] (Location cloc) { return getParseTree(cloc, pool); },
        [&] (Token tok) { return pool.pushBack(tok); },
        [&] (EmptyChild) { return nullParseTree(loc.pos, rule.rhs[i], pool); },
        [&] (ErrorChild) { return errorParseTree(curr->prev->pos, loc.pos, pool); },
        [&] (monostate) -> ParseTree* { assert(false); }
      }, curr->child);
      children.push_back(child);

      loc = curr->prev.value();
      curr = &dpa[loc.pos][loc.i];
    }
    assert(curr->state.rulePos == 0);
    assert(!curr->prev.has_value());

    // Link nodes together
    ParseTree** last = &res->c;
    for (auto rit = children.rbegin(); rit != children.rend(); rit++) {
      *last = *rit;
      last = &(*rit)->s;
    }

    return res;
  }

  // Constructs a parse tree for the `startSymbol`. If there are none, returns `nullptr`.
  ParseTree* EarleyParser::getParseTree(Core::Allocator<ParseTree>& pool) const {
    return fin ? getParseTree(*fin, pool) : nullptr;
  }

  #undef assert

  vector<EarleyParser::ErrorInfo> EarleyParser::popErrors() {
    vector<ErrorInfo> res;
    res.swap(errors);
    return res;
  }

  string EarleyParser::showState(const State& s, const vector<string>& names) const {
    string res = std::to_string(s.startPos) + ", " + names.at(rules[s.ruleIndex].lhs) + " ::= ";
    for (size_t i = 0; i < rules[s.ruleIndex].rhs.size(); i++) {
      if (i == s.rulePos) res += "|";
      res += names.at(rules[s.ruleIndex].rhs[i]);
    }
    if (s.rulePos == rules[s.ruleIndex].rhs.size()) res += "|";
    return res;
  }

  string EarleyParser::showStates(const vector<string>& names) const {
    if (dpa.size() != str.size() + 1) throw Core::Unreachable();
    string res = "";
    for (size_t pos = 0; pos <= str.size(); pos++) {
      res += "States at position " + std::to_string(pos) + ":\n";
      for (const LinkedState& ls: dpa[pos]) res += showState(ls.state, names) + "\n";
      res += "\n";
      if (pos < str.size()) res += "Next token: " + names.at(str[pos].id) + "\n";
    }
    return res;
  }

}
