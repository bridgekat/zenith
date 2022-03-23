// Parsing :: Rule, EarleyParser

#ifndef PARSER_HPP_
#define PARSER_HPP_

#include <optional>
#include <variant>
#include <functional>
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
    bool active = true;
  };

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

    // Production rules
    vector<Rule> rules;
    // Starting symbol
    Symbol startSymbol;

    // Token stream
    Lexer* lexer;
    // Ignored token ID
    optional<Symbol> ignoredSymbol;

    EarleyParser(Lexer* lexer):
      rules(), startSymbol(0), lexer(lexer), ignoredSymbol(),
      numSymbols(0), nullableRule(), sorted(), firstRule(), totalLength(),
      sentence(), dpa(), errors(), ambiguities() {}
    EarleyParser(const EarleyParser&) = default;
    EarleyParser& operator=(const EarleyParser&) = default;
    virtual ~EarleyParser() = default;

    bool eof() const noexcept { return lexer->eof(); }

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
      // TODO: store more information about ambiguity? (e.g. at least one alternative parse)
      bool ambiguous;
    };

    // Maintained states (TODO: maintain?)
    Symbol numSymbols;
    vector<optional<size_t>> nullableRule;
    vector<size_t> sorted, firstRule, totalLength;

    // Ephemeral states
    vector<ParseTree> sentence;
    vector<vector<LinkedState>> dpa;

    vector<ErrorInfo> errors;
    vector<AmbiguityInfo> ambiguities;

    // The parsing algorithm
    size_t toCharsStart(size_t pos) const noexcept;
    size_t toCharsEnd(size_t pos) const noexcept;
    optional<ErrorInfo> lastError();
    void process();
    optional<pair<Location, size_t>> run();

    // Parse tree generation
    ParseTree* nullParseTree(size_t pos, Symbol id, Core::Allocator<ParseTree>& pool) const;
    ParseTree* getParseTree(Location loc, Core::Allocator<ParseTree>& pool);

    // Debug output
    string showState(const State& s, const vector<string>& names) const;
  };

}

#endif // PARSER_HPP_
