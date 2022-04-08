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

  // See: https://en.cppreference.com/w/cpp/utility/variant/visit
  template <typename... Ts> struct Matcher: Ts... { using Ts::operator()...; };


  // Parse greedily, until there are no further possibilities.
  // Parsing is considered successful only when the last position contains a completed root symbol.
  // This is sometimes unsound, but I could not think of a better way of doing it.
  // (Trying to parse the whole file in one go makes dynamic parsing rules difficult,
  //  and it turned out to be a even more tangled mess...)

  ParseTree* EarleyParser::nextSentence(Core::Allocator<ParseTree>& pool) {
    optional<ErrorInfo> error;
    process();
    while (!eof()) {
      auto [index, nextToken] = run();
      if (index) { // Successful parse
        if (error) errors.push_back(*error);
        if (sentence.empty()) throw Core::Unreachable("EarleyParser: nullable sentences can lead to infinite loop");
        return getParseTree(Location{ dpa.size() - 1, *index }, pool);
      }
      if (!nextToken) { // EOF
        if (!sentence.empty()) { // EOF with incomplete sentence
          if (!error) error = lastError(sentence.back().endPos, sentence.back().endPos, nullopt);
          else error->endPos = sentence.back().endPos;
        }
        break;
      }
      // Error (!index && nextToken)
      if (!error) error = lastError(nextToken->startPos, nextToken->endPos, nextToken->id);
      else error->endPos = nextToken->endPos;
      if (sentence.empty()) {
        // Skip at least one token to avoid infinite loops
        auto tok = lexer.nextToken();
        while (tok && tok->id == ignoredSymbol) tok = lexer.nextToken();
      }
    }
    if (error) errors.push_back(*error);
    return nullptr;
  }

  // For use in `nextSentence()` only
  EarleyParser::ErrorInfo EarleyParser::lastError(size_t startPos, size_t endPos, const optional<Symbol>& got) const {
    if (dpa.size() != sentence.size() + 1) throw Core::Unreachable();
    size_t pos = sentence.size();

    vector<Symbol> expected;
    for (const LinkedState& ls: dpa[pos]) {
      const State& s = ls.state;
      const Rule& rule = rules[s.ruleIndex];
      if (s.rulePos < rule.rhs.size()) expected.push_back(rule.rhs[s.rulePos]);
    }
    std::sort(expected.begin(), expected.end());
    size_t len = std::unique(expected.begin(), expected.end()) - expected.begin();
    expected.resize(len);

    return ErrorInfo(startPos, endPos, expected, got);
  }

  vector<EarleyParser::ErrorInfo> EarleyParser::popErrors() {
    vector<ErrorInfo> res;
    res.swap(errors);
    return res;
  }

  vector<EarleyParser::AmbiguityInfo> EarleyParser::popAmbiguities() {
    vector<AmbiguityInfo> res;
    res.swap(ambiguities);
    return res;
  }

  size_t EarleyParser::toCharsStart(size_t pos) const noexcept {
    if (pos >= sentence.size()) return sentence.empty()? 0 : sentence.back().endPos;
    return sentence[pos].startPos;
  }

  size_t EarleyParser::toCharsEnd(size_t pos) const noexcept {
    if (pos >= sentence.size()) return sentence.empty()? 0 : sentence.back().endPos;
    return sentence[pos].endPos;
  }

  // See: https://en.wikipedia.org/wiki/Earley_parser#The_algorithm (for an overview)
  // See: https://loup-vaillant.fr/tutorials/earley-parsing/ (for a simple way to deal with ε rules)
  // Other related information:
  //   https://github.com/jeffreykegler/kollos/blob/master/notes/misc/leo2.md
  //   https://jeffreykegler.github.io/Marpa-web-site/
  //   https://arxiv.org/pdf/1910.08129.pdf
  // (I am not going to dig too deep into the theories about different parsing algorithms now!)

  void EarleyParser::process() {
    const size_t m = rules.size();

    // Find the number of symbols involved
    numSymbols = startSymbol + 1;
    for (const auto& [lhs, rhs, prec, active]: rules) {
      numSymbols = std::max(numSymbols, lhs + 1);
      for (Symbol sym: rhs) numSymbols = std::max(numSymbols, sym + 1);
    }

    // Work out "nullable" nonterminals and their nullable rules (O(|G|²))
    // Currently we don't care about ambiguous nullables!
    nullableRule = vector<optional<size_t>>(numSymbols, nullopt);
    bool updates = false;
    do {
      updates = false;
      for (size_t i = 0; i < rules.size(); i++) {
        Symbol lhs = rules[i].lhs;
        const auto& rhs = rules[i].rhs;
        if (!nullableRule[lhs].has_value()) {
          bool f = true;
          for (Symbol sym: rhs) {
            if (!nullableRule[sym].has_value()) { f = false; break; }
          }
          if (f) {
            nullableRule[lhs] = i;
            updates = true;
          }
        }
      }
    } while (updates);

    // Sort all rules by nonterminal ID (for faster access in `run()`)
    sorted.clear();
    for (size_t i = 0; i < m; i++) sorted.push_back(i);
    std::sort(sorted.begin(), sorted.end(), [this] (size_t a, size_t b) { return rules[a].lhs < rules[b].lhs; });

    // For each nonterminal find the index of its first production rule (for faster access in `run()`, if none then set to `m`)
    // Also accumulate the lengths of RHS (plus one) of the production rules (for better hashing in `run()`)
    firstRule = vector<size_t>(numSymbols, m);
    totalLength = vector<size_t>(m, 0);
    for (size_t i = 0; i < m; i++) {
      const auto& [lhs, rhs, prec, active] = rules[sorted[i]];
      if (firstRule[lhs] == m) firstRule[lhs] = i;
      if (i + 1 < m) totalLength[i + 1] = totalLength[i] + rhs.size() + 1;
    }
  }

  // Pre: `numSymbols`, `nullableRule`, `sorted`, `firstRule` and `totalLength` must be
  //   consistent with currently active rules.
  pair<optional<size_t>, optional<ParseTree>> EarleyParser::run() {
    optional<ParseTree> nextToken = nullopt;

    sentence.clear();
    dpa.clear();

    // A minor optimization: avoid looking up rules multiple times (see below)
    vector<Symbol> added;
    vector<bool> isAdded(numSymbols, false);

    // A hash function for DP states
    auto hash = [this] (const State& x) { return x.startPos * 524287u + (totalLength[x.ruleIndex] + x.rulePos); };
    unordered_map<State, size_t, decltype(hash)> mp(0, hash);

    // Initial states
    dpa.emplace_back();
    for (size_t i = firstRule[startSymbol]; i < sorted.size() && rules[sorted[i]].lhs == startSymbol; i++) {
      const size_t rid = sorted[i];
      if (!rules[rid].active) continue;
      State s{ 0, rid, 0 };
      mp[s] = dpa[0].size();
      dpa[0].emplace_back(s, nullopt, monostate{});
    }

    // Invariant: `mp` maps all elements of `states[pos]` to their indices
    for (size_t pos = 0; ; pos++) {

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
            // Add all active rules for `sym`
            for (size_t j = firstRule[sym]; j < sorted.size() && rules[sorted[j]].lhs == sym; j++) {
              const size_t rid = sorted[j];
              if (!rules[rid].active) continue;
              State ss{ pos, rid, 0 };
              if (!mp.contains(ss)) {
                mp[ss] = dpa[pos].size();
                dpa[pos].emplace_back(ss, nullopt, monostate{});
              }
            }
          }
          // If `sym` is nullable, we could skip it (empty completion)
          if (nullableRule[sym].has_value()) {
            State ss{ s.startPos, s.ruleIndex, s.rulePos + 1 };
            // Calculate new cost
            size_t numDisrespects = dpa[pos][i].numDisrespects;
            if (rules[s.ruleIndex].lhs == sym &&
                rules[s.ruleIndex].prec > rules[*nullableRule[sym]].prec)
              numDisrespects += rules[s.ruleIndex].prec - rules[*nullableRule[sym]].prec;
            // New linked state
            LinkedState lss{ ss, Location{ pos, i }, monostate{}, numDisrespects };
            if (!mp.contains(ss)) {
              mp[ss] = dpa[pos].size();
              dpa[pos].push_back(lss);
            } else {
              // Ambiguity detected
              LinkedState& lsso = dpa[pos][mp[ss]];
              int res = disambiguate(pos, lsso, lss);
              if (res > 0) lsso = lss;
              if (res == 0) lsso.unresolved = true;
            }
          }
        } else {
          // Perform nonempty completion
          if (derived.empty()) continue;
          Symbol sym = rules[s.ruleIndex].lhs;
          size_t posj = s.startPos;
          for (size_t j = 0; j < dpa[posj].size(); j++) {
            State t = dpa[posj][j].state;
            const auto& tderived = rules[t.ruleIndex].rhs;
            if (t.rulePos < tderived.size() && tderived[t.rulePos] == sym) {
              State tt{ t.startPos, t.ruleIndex, t.rulePos + 1 };
              // Calculate new cost
              size_t numDisrespects = dpa[posj][j].numDisrespects + dpa[pos][i].numDisrespects;
              if (rules[t.ruleIndex].lhs == sym &&
                  rules[t.ruleIndex].prec > rules[s.ruleIndex].prec)
                numDisrespects += rules[t.ruleIndex].prec - rules[s.ruleIndex].prec;
              // New linked state
              LinkedState ltt{ tt, Location{ posj, j }, Location{ pos, i }, numDisrespects };
              if (!mp.contains(tt)) {
                mp[tt] = dpa[pos].size();
                dpa[pos].push_back(ltt);
              } else {
                // Ambiguity detected
                LinkedState& ltto = dpa[pos][mp[tt]];
                int res = disambiguate(pos, ltto, ltt);
                if (res > 0) ltto = ltt;
                if (res == 0) ltto.unresolved = true;
              }
            }
          }
        }
      }
      // Clear flags
      for (Symbol sym: added) isAdded[sym] = false;
      added.clear();

      // Advance to next position
      size_t restore = lexer.position();
      nextToken = lexer.nextToken();
      while (nextToken && nextToken->id == ignoredSymbol) nextToken = lexer.nextToken();
      if (!nextToken) break; // EOF
      sentence.push_back(*nextToken);

      // "Scanning" stage
      // Also updating `mp` to reflect `states[pos + 1]` instead
      dpa.emplace_back();
      mp.clear();
      for (size_t i = 0; i < dpa[pos].size(); i++) {
        State s = dpa[pos][i].state;
        const auto& derived = rules[s.ruleIndex].rhs;
        if (s.rulePos < derived.size() && derived[s.rulePos] == nextToken->id) {
          State ss{ s.startPos, s.ruleIndex, s.rulePos + 1 };
          // No need to check for presence! `s` is already unique.
          mp[ss] = dpa[pos + 1].size();
          dpa[pos + 1].emplace_back(ss, Location{ pos, i }, *nextToken, dpa[pos][i].numDisrespects);
        }
      }
      if (dpa[pos + 1].empty()) { // Error
        lexer.setPosition(restore);
        sentence.pop_back();
        dpa.pop_back();
        break;
      }
    }

    // Check if the start symbol completes
    optional<size_t> res = nullopt;
    for (size_t i = 0; i < dpa.back().size(); i++) {
      const State& s = dpa.back()[i].state;
      const Rule& rule = rules[s.ruleIndex];
      if (s.startPos == 0 && rule.lhs == startSymbol && s.rulePos == rule.rhs.size()) {
        res = i;
        break;
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
    *       - nullable nonterminal: by IH (2) + skipping at the "prediction/completion" stage.
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

    return { res, nextToken };
  }

  // A helper function that gives a preference between two alternative links
  // Returns -1 to keep old, 1 to use new, 0 for unresolved (keeping old)
  int EarleyParser::disambiguate(size_t pos, const LinkedState& old, const LinkedState& curr) const noexcept {
    const Rule& rule = rules[old.state.ruleIndex];
    // if (old.state != curr.state) throw Core::Unreachable();
    if      (old.numDisrespects < curr.numDisrespects) return -1;
    else if (old.numDisrespects > curr.numDisrespects) return 1;
    else {
      bool rl = (rule.prec % 2 != 0); // Odd number denotes "rightmost longest"
      size_t oldLength = pos - old.prev->pos;
      size_t currLength = pos - curr.prev->pos;
      if (rl) return currLength > oldLength?  1 : currLength < oldLength ? -1 : 0;
      else    return currLength > oldLength? -1 : currLength < oldLength ?  1 : 0;
    }
  }

  #define assert(expr) if (!(expr)) throw Core::Unreachable()

  // Constructs an empty parse tree for a nullable symbol.
  ParseTree* EarleyParser::nullParseTree(size_t pos, Symbol id, Core::Allocator<ParseTree>& pool) const {

    // Must be a nullable symbol
    assert(nullableRule[id].has_value());
    size_t ruleIndex = nullableRule[id].value();

    // Current node
    ParseTree* res = pool.pushBack(ParseTree{
      nullptr, nullptr,
      id,
      nullopt, nullopt, ruleIndex,
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

  // Constructs a parse tree for a completed DP state.
  ParseTree* EarleyParser::getParseTree(Location loc, Core::Allocator<ParseTree>& pool) {
    const LinkedState* curr = &dpa[loc.pos][loc.i];
    const Rule& rule = rules[curr->state.ruleIndex];

    // Must be a completed state
    assert(curr->state.rulePos == rule.rhs.size());

    // Current node
    ParseTree* res = pool.pushBack(ParseTree{
      nullptr, nullptr,
      rule.lhs,
      nullopt, nullopt, curr->state.ruleIndex,
      toCharsStart(curr->state.startPos),
      loc.pos == 0 ? toCharsStart(0) : toCharsEnd(loc.pos - 1)
    });

    // Follow links to construct a list of children (in reverse order)
    vector<ParseTree*> children;
    for (size_t i = rule.rhs.size(); i --> 0;) {
      assert(curr->prev.has_value());

      // Check for unresolved ambiguity
      if (curr->unresolved) {
        ambiguities.emplace_back(
          toCharsStart(curr->state.startPos),
          loc.pos == 0 ? toCharsStart(0) : toCharsEnd(loc.pos - 1)
        );
      }

      // Get child parse tree
      ParseTree* child = visit(Matcher{
        [&] (Location cloc) { return getParseTree(cloc, pool); },
        [&] (ParseTree tok) { return pool.pushBack(tok); },
        [&] (monostate) { return nullParseTree(loc.pos, rule.rhs[i], pool); }
      }, curr->child);
      children.push_back(child);

      // Backward step
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

  #undef assert

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
    if (dpa.size() != sentence.size() + 1) throw Core::Unreachable();
    string res = "";
    for (size_t pos = 0; pos <= sentence.size(); pos++) {
      res += "States at position " + std::to_string(pos) + ":\n";
      for (const LinkedState& ls: dpa[pos]) res += showState(ls.state, names) + " (" + std::to_string(ls.numDisrespects) + ")" + "\n";
      res += "\n";
      if (pos < sentence.size()) res += "Next token: " + names.at(sentence[pos].id) + "\n";
    }
    return res;
  }

}
