// Parsing :: Rule, EarleyParser

#ifndef PARSER_HPP_
#define PARSER_HPP_

#include <limits>
#include <optional>
#include <core/base.hpp>
#include "lexer.hpp"

namespace Parsing {

  using Symbol = size_t;
  using Precedence = uint16_t;

  struct ParserError {
    size_t startPos;
    size_t endPos;
    std::vector<Symbol> expected;
    std::optional<Symbol> got;
  };

  // This is more suitable for left-recursive grammars than right-recursive ones.
  // For more details see implementation (`parser.cpp`).
  class EarleyParser {
  public:
    struct Pattern {
      std::pair<Symbol, Precedence> sym;
    };
    struct Rule {
      std::pair<Symbol, Precedence> lhs;
      std::vector<std::pair<Symbol, Precedence>> rhs;
    };
    struct State {
      size_t startPos;
      size_t rule;
      size_t progress;
    };
    struct Location {
      size_t pos;
      size_t index;
    };
    struct LinkedState {
      State state;
      std::vector<std::pair<Location, Location>> links;
    };

    // Special location indicating a token (leaf node).
    static constexpr auto Leaf = Location{std::numeric_limits<size_t>::max(), std::numeric_limits<size_t>::max()};

    // The given Lexer reference must be valid over the EarleyParser's lifetime.
    EarleyParser(Lexer& lexer):
      mLexer(lexer) {}

    auto lexer() const -> Lexer const& { return mLexer; }
    auto eof() const -> bool { return mLexer.eof(); }

    auto startSymbol() const -> Symbol { return mStartSymbol; }
    auto setStartSymbol(Symbol sym) -> void { mStartSymbol = sym, mDirty = true; }

    auto ignoredSymbol() const -> Symbol { return mIgnoredSymbol; }
    auto setIgnoredSymbol(Symbol sym) -> void { mIgnoredSymbol = sym, mDirty = true; }

    auto pattern(size_t i) const -> Pattern const& { return mPatterns[i]; }
    auto clearPatterns() -> void { mPatterns.clear(), mDirty = true; }
    auto addPattern(Symbol sym, Precedence prec) -> size_t {
      auto id = mPatterns.size();
      mPatterns.push_back(Pattern{std::make_pair(sym, prec)});
      mDirty = true;
      return id;
    }

    auto rule(size_t i) const -> Rule const& { return mRules[i]; }
    auto clearRules() -> void { mRules.clear(), mDirty = true; }
    auto addRule(Symbol sym, Precedence prec, std::vector<std::pair<Symbol, Precedence>> derived) -> size_t {
      auto id = mRules.size();
      mRules.push_back(Rule{std::make_pair(sym, prec), std::move(derived)});
      mDirty = true;
      return id;
    }

    auto sentence() const -> std::vector<Token> const& { return mSentence; }
    auto forest() const -> std::vector<std::vector<LinkedState>> const& { return mDP; }
    auto popErrors() -> std::vector<ParserError> { return std::exchange(mErrors, {}); }

    // Run parsing algorithm.
    auto nextSentence() -> bool;

    // Debug output.
    auto showState(LinkedState const& ls, std::vector<std::string> const& names) const -> std::string;
    auto showStates(std::vector<std::string> const& names) const -> std::string;

  private:
    Lexer& mLexer;                  // Token stream.
    Symbol mStartSymbol = 0;        // Starting symbol ID.
    Symbol mIgnoredSymbol = 0;      // Ignored symbol ID.
    std::vector<Pattern> mPatterns; // Pattern ID -> (symbol ID, precedence).
    std::vector<Rule> mRules;       // Rule ID -> (LHS symbols ID, RHS symbols IDs).

    bool mDirty = true;                            // Patterns or rules changed, the following need to be updated:
    Symbol mNumSymbols = 0;                        // (Maximum symbol ID occured in patterns and rules) + 1.
    std::vector<std::optional<size_t>> mEmptyRule; // LHS symbol ID -> empty rule ID.
    std::vector<size_t> mSorted;                   // Indices of non-empty rules, sorted by LHS symbol ID.
    std::vector<size_t> mFirstRule;                // LHS symbol ID -> index in `mSorted`.
    std::vector<size_t> mTotalLength;              // LHS symbol ID -> total length of RHS.

    std::vector<Token> mSentence;              // Parsed tokens.
    std::vector<std::vector<LinkedState>> mDP; // The DP array, aka. "shared packed parse forest (SPPF)".
    std::vector<ParserError> mErrors;          // Parsing errors.

    // The parsing algorithm.
    auto process() -> void;
    auto run() -> std::pair<bool, std::optional<Token>>;
    auto lastError(size_t startPos, size_t endPos, std::optional<Symbol> const& got) const -> ParserError;
  };

}

#endif // PARSER_HPP_
