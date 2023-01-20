// Parsing :: Grammar, GrammarBuilder, Node, Parser...

#ifndef PARSER_HPP_
#define PARSER_HPP_

#include <limits>
#include <list>
#include <optional>
#include <unordered_map>
#include <variant>
#include <common.hpp>
#include "lexer.hpp"
#include "stream.hpp"

namespace Parsing {

  // Preprocessed context-free grammar for use by `Parser`.
  struct Grammar {
    struct Rule {
      std::pair<Symbol, Precedence> lhs;              // LHS symbol.
      std::vector<std::pair<Symbol, Precedence>> rhs; // RHS symbols.
    };
    struct IndexRange {
      size_t begin; // Index of the first rule that corresponds to this symbol.
      size_t end;   // Index of the last rule that corresponds to this symbol + 1.
    };
    Symbol numSymbols;              // Number of symbols = (maximum symbol ID occured in rules) + 1.
    Symbol startSymbol;             // Starting symbol ID.
    Symbol ignoredSymbol;           // Ignored symbol ID.
    std::vector<Rule> rules;        // Rule ID -> (LHS symbol, RHS symbols).
    std::vector<size_t> sorted;     // Indices of non-nullable rules, sorted by LHS symbol.
    std::vector<IndexRange> ranges; // LHS symbol ID -> rule index ranges in `sorted`.
  };

  // Grammar preprocessor.
  class GrammarBuilder {
  public:
    auto withStartSymbol(Symbol value) -> GrammarBuilder&;
    auto withIgnoredSymbol(Symbol value) -> GrammarBuilder&;
    auto withRule(std::pair<Symbol, Precedence> lhs, std::vector<std::pair<Symbol, Precedence>> const& rhs)
      -> GrammarBuilder&;

    // Constructs a well-formed `Grammar`.
    auto make() const -> Grammar;

  private:
    Symbol _startSymbol = 0;
    Symbol _ignoredSymbol = 0;
    std::vector<Grammar::Rule> _rules;
  };

  // A left-match SPPF node emitted by a parser.
  // All pointers should be non-empty and valid.
  struct Node {
    struct State {
      size_t begin;    // Start index in sentence.
      size_t end;      // End index in sentence.
      size_t rule;     // Production rule ID.
      size_t progress; // Matching position in production rule.
      friend auto operator==(State const&, State const&) -> bool = default;
      struct Hasher {
        auto operator()(State const& s) const -> size_t { return hashAll(s.begin, s.end, s.rule, s.progress); }
      };
    };
    State state;                                                   // Payload.
    std::list<std::pair<Node*, std::variant<Node*, Token*>>> next; // Forward links (construction deferred).
    std::list<std::pair<Node*, std::variant<Node*, Token*>>> prev; // Backward links.
  };

  // Earley parser!
  // Without "Leo's optimisation", this is more suitable for left-recursive rules (linear complexity)
  // than right-recursive ones (quadratic time and space complexity w.r.t. length of the sentence).
  class Parser {
  public:
    // Given references must be valid over the `Parser`'s lifetime.
    Parser(Grammar const& grammar, Stream<std::optional<Token>>& stream):
      _grammar(grammar),
      _stream(stream) {}

    auto eof() const -> bool { return _stream.eof(); }
    auto advance() -> bool;

    // Retrieves results.
    auto tokens() const -> std::list<Token> const& { return _tokens; }
    auto nodes() const -> std::vector<std::list<Node>> const& { return _nodes; }

    // Debug output.
    auto showState(Node const& node, std::vector<std::string> const& names) const -> std::string;
    auto showStates(std::vector<std::string> const& names) const -> std::string;

  private:
    Grammar const& _grammar;               // Grammar.
    Stream<std::optional<Token>>& _stream; // Input `Token` stream.
    std::list<Token> _tokens;              // Parsed tokens.
    std::vector<std::list<Node>> _nodes;   // The DP array, aka. "shared packed parse forest (SPPF)".

    // Map for state deduplication: state -> node.
    std::unordered_map<Node::State, Node*, Node::State::Hasher> _map;
    // Map of completion candidates: (end position, next symbol) -> node.
    std::unordered_multimap<std::pair<size_t, Symbol>, Node*, PairHasher> _completions;
    // Map of null-completed nodes: (start and end position, symbol) -> node.
    std::unordered_multimap<std::pair<size_t, Symbol>, Node*, PairHasher> _completed;

    auto _nextToken() -> std::optional<Token>;
    auto _node(size_t begin, size_t end, size_t rule, size_t progress) -> Node*;
    auto _transition(Node* prev, std::variant<Node*, Token*> child, Node* next) -> void;
    auto _run() -> bool;
    auto _prune() -> void;
  };

}

#endif // PARSER_HPP_
