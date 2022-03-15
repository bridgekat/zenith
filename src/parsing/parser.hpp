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
    vector<Rule> rules;
    Symbol start;

    EarleyParser(): rules(), start(0), str(), nullable(), dpa() {}

    ParseTree* parse(const vector<Token>& str, Core::Allocator<ParseTree>& pool);

  // private:
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
      variant<Location, Token, monostate> child;
      bool ambiguous; // TODO: more information about ambiguity?
    };
    // Ephemeral states
    vector<Token> str;
    vector<optional<size_t>> nullable;
    vector<vector<LinkedState>> dpa;

    // The parsing algorithm
    size_t toCharsStart(size_t pos) const noexcept;
    size_t toCharsEnd(size_t pos) const noexcept;
    void run();
    ParseTree* nullParseTree(size_t pos, Symbol id, Core::Allocator<ParseTree>& pool) const;
    ParseTree* getParseTree(Location loc, Core::Allocator<ParseTree>& pool) const;
    ParseTree* getParseTree(Core::Allocator<ParseTree>& pool) const;

    // Debug output
    string showState(const State& s, const vector<string>& names) const;
  };

}

#endif // PARSER_HPP_
