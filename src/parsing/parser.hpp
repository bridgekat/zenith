// Parsing :: Rule, EarleyParser

#ifndef PARSER_HPP_
#define PARSER_HPP_

#include <optional>
#include <variant>
#include <core/base.hpp>
#include "lexer.hpp"


namespace Parsing {

  using std::vector;
  using std::optional;
  using std::variant;
  using std::monostate;


  // Nonterminal symbol production rule
  struct Rule {
    Symbol lhs;
    vector<Symbol> rhs;
    size_t prec = 0;
    bool active = true;
  };

  // Convert floating-point precedence in the range [0, 1] to `size_t` in the range [0, 4096)
  // (precision can be specified in the function below)
  inline size_t makePrec(double prec, bool rightmostLongest) noexcept {
    constexpr size_t maxPrec = 4096 / 2 - 1;
    size_t res = prec * maxPrec;                    // `res` is now in [0, 2048)
    return rightmostLongest? res * 2 + 1 : res * 2; // Odd number denotes "rightmost longest"
  }

  // This is more suitable for left-recursive grammars than right-recursive ones.
  // For more details see implementation (`parser.cpp`).
  class EarleyParser {
  public:
    struct ErrorInfo {
      size_t startPos, endPos;
      vector<Symbol> expected;
      optional<Symbol> got;
      ErrorInfo(size_t startPos, size_t endPos, const vector<Symbol>& expected, const optional<Symbol>& got):
        startPos(startPos), endPos(endPos), expected(expected), got(got) {}
    };
    struct AmbiguityInfo {
      size_t startPos, endPos;
      AmbiguityInfo(size_t startPos, size_t endPos):
        startPos(startPos), endPos(endPos) {}
    };

    // Token stream
    Lexer& lexer;
    // Production rules
    vector<Rule> rules;
    // Starting symbol ID
    Symbol startSymbol;
    // Ignored token ID (optional)
    optional<Symbol> ignoredSymbol;

    // The given Lexer reference must be valid over the EarleyParser's lifetime.
    EarleyParser(Lexer& lexer):
      lexer(lexer), rules(), startSymbol(0), ignoredSymbol(),
      numSymbols(0), nullableRule(), sorted(), firstRule(), totalLength(),
      sentence(), dpa(), errors(), ambiguities() {}

    bool eof() const noexcept { return lexer.eof(); }

    // Constructs a parse tree for `startSymbol`. Returns `nullptr` if reached end-of-file.
    // All errors will be logged
    ParseTree* nextSentence(Core::Allocator<ParseTree>& pool);

    // Get and clear error log
    vector<ErrorInfo> popErrors();
    vector<AmbiguityInfo> popAmbiguities();

    // Debug output
    string showStates(const vector<string>& names) const;

  private:
    // DP (dynamic programming) state
    struct State {
      size_t startPos, ruleIndex, rulePos;
      auto operator<=>(const State& r) const = default;
    };
    // Location in DP array
    struct Location { size_t pos, i; };
    // State with transition source links
    struct LinkedState {
      State state;
      optional<Location> prev;
      variant<Location, ParseTree, monostate> child;
      size_t numDisrespects = 0; // The "cost" of a parse, used in disambiguation
      bool unresolved = false;   // TODO: store more information about unresolved ambiguity? (e.g. at least one alternative parse)
    };

    // Ephemeral states
    Symbol numSymbols;
    vector<optional<size_t>> nullableRule;
    vector<size_t> sorted, firstRule, totalLength;
    vector<ParseTree> sentence;
    vector<vector<LinkedState>> dpa;

    // Error logs
    vector<ErrorInfo> errors;
    vector<AmbiguityInfo> ambiguities;

    ErrorInfo lastError(size_t startPos, size_t endPos, const optional<Symbol>& got) const;
    size_t toCharsStart(size_t pos) const noexcept;
    size_t toCharsEnd(size_t pos) const noexcept;

    // The parsing algorithm
    void process();
    pair<optional<size_t>, optional<ParseTree>> run();
    int disambiguate(size_t pos, const LinkedState& old, const LinkedState& curr) const noexcept;
    
    // Parse tree construction
    ParseTree* nullParseTree(size_t pos, Symbol id, Core::Allocator<ParseTree>& pool) const;
    ParseTree* getParseTree(Location loc, Core::Allocator<ParseTree>& pool);

    // Debug output
    string showState(const State& s, const vector<string>& names) const;
  };

}

#endif // PARSER_HPP_
