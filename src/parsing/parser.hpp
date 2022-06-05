// Parsing :: Rule, EarleyParser

#ifndef PARSER_HPP_
#define PARSER_HPP_

#include <optional>
#include <core/base.hpp>
#include "lexer.hpp"


namespace Parsing {

  using std::vector;
  using std::optional;


  using Symbol = size_t;
  using Prec = uint16_t;

  // This is more suitable for left-recursive grammars than right-recursive ones.
  // For more details see implementation (`parser.cpp`).
  class EarleyParser {
  public:
    struct Rule { pair<Symbol, Prec> lhs; vector<pair<Symbol, Prec>> rhs; };
    struct State { size_t startPos, rule, progress; };
    struct Location { size_t pos, i; };
    struct LinkedState { State state; vector<pair<Location, Location>> links; };
    struct ErrorInfo { size_t startPos, endPos; vector<Symbol> expected; optional<Symbol> got; };
    static constexpr Location Leaf{ static_cast<size_t>(-1), static_cast<size_t>(-1) };

    // The given Lexer reference must be valid over the EarleyParser's lifetime.
    EarleyParser(Lexer& lexer):
      lexer(lexer), startSymbol(0), ignoredSymbol(0), patterns(), rules(),
      dirty(true), numSymbols(0), emptyRule(), sorted(), firstRule(), totalLength(),
      sentence(), dpa(), errors() {}

    void setStartSymbol(Symbol sym) noexcept { startSymbol = sym; dirty = true; }
    void setIgnoredSymbol(Symbol sym) noexcept { ignoredSymbol = sym; dirty = true; }

    size_t addPattern(Symbol sym, Prec prec) {
      size_t id = patterns.size();
      patterns.emplace_back(sym, prec);
      dirty = true;
      return id;
    }

    size_t addRule(Symbol sym, Prec prec, vector<pair<Symbol, Prec>> derived) {
      size_t id = rules.size();
      rules.push_back(Rule{ { sym, prec }, std::move(derived) });
      dirty = true;
      return id;
    }

    void clearPatterns() noexcept { patterns.clear(); dirty = true; }
    void clearRules() noexcept { rules.clear(); dirty = true; }

    // State getters (references remain valid until state change)
    bool eof() const noexcept { return lexer.eof(); }
    auto getStartSymbol() const noexcept { return startSymbol; }
    auto getIgnoredSymbol() const noexcept { return ignoredSymbol; }
    const auto& getPattern(size_t i) const noexcept { return patterns[i]; }
    const auto& getRule(size_t i) const noexcept { return rules[i]; }

    // Result getters (referred data remain unchanged until next parse)
    const auto& getSentence() const noexcept { return sentence; }
    const auto& getForest() const noexcept { return dpa; }
    auto popErrors() { return std::exchange(errors, {}); }

    // Run parsing algorithm
    bool nextSentence();

    // Debug output
    string showState(const LinkedState& ls, const vector<string>& names) const;
    string showStates(const vector<string>& names) const;

  private:
    Lexer& lexer;                                   // Token stream
    Symbol startSymbol, ignoredSymbol;              // Starting & ignored symbol ID
    vector<pair<Symbol, Prec>> patterns;            // Pattern ID -> symbol mapping
    vector<Rule> rules;                             // Production rules

    bool dirty;                                     // Patterns or rules changed, the following need to be updated:
    Symbol numSymbols;                              // (Maximum symbol ID occured in patterns and rules) + 1
    vector<optional<size_t>> emptyRule;             // Symbol ID -> empty rule ID
    vector<size_t> sorted, firstRule, totalLength;  // Records non-empty rules

    vector<Token> sentence;                         // Parsed tokens
    vector<vector<LinkedState>> dpa;                // The DP array (aka. "shared packed parse forest (SPPF)")
    vector<ErrorInfo> errors;                       // Parsing errors

    // The parsing algorithm
    void process();
    pair<bool, optional<Token>> run();
    ErrorInfo lastError(size_t startPos, size_t endPos, const optional<Symbol>& got) const;
  };

}

#endif // PARSER_HPP_
