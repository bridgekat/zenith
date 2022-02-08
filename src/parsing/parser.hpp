// Parsing :: EarleyParser

#ifndef PARSER_HPP_
#define PARSER_HPP_

#include "lexer.hpp"


namespace Parsing {

  // This is more suitable for left-recursive grammars than right-recursive ones.
  // For more details see implementation (`parser.cpp`).
  class EarleyParser {
  public:
    // Reusing lexer `TokenID` for terminal & nonterminal symbols
    // (A boolean value is used to distinguish terminals from nonterminals)
    struct Symbol {
      bool terminal;
      TokenID index;
      auto operator<=>(const Symbol&) const = default;
    };
    // Nonterminal symbol production rule
    struct Rule {
      TokenID lhs;
      vector<Symbol> rhs;
    };
    // DP (dynamic programming) state
    struct State {
      size_t leftPos, ruleIndex, rulePos;
      auto operator<=>(const State& r) const = default;
    };

    vector<Rule> rules;
    TokenID start;

    EarleyParser(): rules(), start(0) {}

    // Run parsing algorithm, returns the whole DP array
    vector<vector<State>> run(const vector<Token>& str);

    // Debug output
    string showState(const State& s, const vector<string>& terminals, const vector<string>& nonterminals) const;
  };

}

#endif // PARSER_HPP_
