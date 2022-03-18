// Parsing :: EarleyParser, TemplatedParser

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
  };

  // This is more suitable for left-recursive grammars than right-recursive ones.
  // For more details see implementation (`parser.cpp`).
  class EarleyParser {
  public:
    // Error information
    struct ErrorInfo {
      size_t startPos, endPos;
      vector<Symbol> expected;
      optional<Symbol> got;
      ErrorInfo(size_t startPos, size_t endPos, const vector<Symbol>& expected, const optional<Symbol>& got):
        startPos(startPos), endPos(endPos), expected(expected), got(got) {}
    };
    // Ambiguity information
    struct AmbiguityInfo {
      size_t startPos, endPos;
      AmbiguityInfo(size_t startPos, size_t endPos):
        startPos(startPos), endPos(endPos) {}
    };

    // Production rules
    vector<Rule> rules;
    // Starting symbol
    Symbol startSymbol;
    // Optional symbol for erroneous substrings. Will be used for error recovery.
    optional<Symbol> errorSymbol;

    EarleyParser():
      rules(), startSymbol(0), errorSymbol(), str(), nullable(), dpa(), fin(), error(false), errors(), ambiguities() {}
    virtual ~EarleyParser() = default;

    // Computes a possible parse tree. Returns `nullptr` if unable to recover from errors.
    // All errors will be logged
    ParseTree* parse(const vector<Token>& str, Core::Allocator<ParseTree>& pool);
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
    // Empty or error child
    struct EmptyChild {};
    struct ErrorChild {};
    // State with transition source links
    struct LinkedState {
      State state;
      optional<Location> prev;
      variant<Location, Token, EmptyChild, ErrorChild, monostate> child;
      // TODO: store more information about ambiguity? (e.g. at least one alternative parse)
      bool ambiguous;
    };

    // Ephemeral states
    vector<Token> str;
    vector<optional<size_t>> nullable;
    vector<vector<LinkedState>> dpa;
    optional<Location> fin;
    bool error;
    vector<ErrorInfo> errors;
    vector<AmbiguityInfo> ambiguities;

    // The parsing algorithm
    size_t toCharsStart(size_t pos) const noexcept;
    size_t toCharsEnd(size_t pos) const noexcept;
    void logError(size_t pos, size_t endPos);
    void run();

    // Parse tree generation
    ParseTree* nullParseTree(size_t pos, Symbol id, Core::Allocator<ParseTree>& pool) const;
    ParseTree* errorParseTree(size_t startPos, size_t endPos, Core::Allocator<ParseTree>& pool) const;
    ParseTree* getParseTree(Location loc, Core::Allocator<ParseTree>& pool);
    ParseTree* getParseTree(Core::Allocator<ParseTree>& pool);

    // Debug output
    string showState(const State& s, const vector<string>& names) const;
  };

}

#endif // PARSER_HPP_
