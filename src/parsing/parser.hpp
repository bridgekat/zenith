// Parsing :: Grammar, GrammarBuilder, Node, EarleyParser...

#ifndef PARSING_PARSER_HPP_
#define PARSING_PARSER_HPP_

#include <unordered_map>
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
    struct Link {
      size_t sibling; // Index of the previous/next node.
      bool leaf;      // Whether it is a leaf node.
      size_t child;   // Index of completed child node (for non-leaf nodes) or token (for leaf nodes).
    };
    State state;            // Payload.
    std::vector<Link> next; // Forward links (construction deferred).
    std::vector<Link> prev; // Backward links.
  };

  // Earley parser!
  // See: https://en.wikipedia.org/wiki/Earley_parser#The_algorithm for an overview.
  // See: https://loup-vaillant.fr/tutorials/earley-parsing
  // Other related information:
  // - https://github.com/jeffreykegler/old_kollos/blob/master/notes/misc/leo2.md
  // - https://jeffreykegler.github.io/Marpa-web-site/
  // - https://arxiv.org/pdf/1910.08129.pdf
  //
  // Without Leo's optimisation, this is more suitable for left-recursive rules (linear complexity)
  // than right-recursive ones (quadratic time and space complexity w.r.t. length of the sentence).
  class EarleyParser {
  public:
    struct IndexRange {
      size_t begin; // Index of the first node (in the DP array) at this position.
      size_t end;   // Index of the last node (in the DP array) at this position + 1.
    };
    struct ErrorRecoveryParams {
      size_t maxSkipped; // Max number of skipped tokens around an error.
      size_t threshold;  // Number of tokens to be recognised before declaring success.
    };
    struct Error {
      std::vector<Symbol> expected; // Expected symbol IDs (including terminals and nonterminals).
      std::optional<Token> got;     // The problematic token (empty if reached EOF).
    };

    // Given references must be valid over the `Parser`'s lifetime.
    EarleyParser(Grammar const& grammar, IStream<Token>& stream, ErrorRecoveryParams const& params):
      _grammar(grammar),
      _marked(stream),
      _params(params) {}

    // Parse with error recovery.
    auto parse() -> bool;

    // Retrieves results.
    auto tokens() const -> std::vector<Token> const& { return _tokens; }
    auto nodes() const -> std::vector<Node> const& { return _nodes; }
    auto ranges() const -> std::vector<IndexRange> const& { return _ranges; }
    auto errors() const -> std::vector<Error> const& { return _errors; }
    auto finalStates() const -> std::vector<size_t>;

    // Debug output.
    auto showState(Node const& node, std::vector<std::string> const& names) const -> std::string;
    auto showStates(std::vector<std::string> const& names) const -> std::string;

  private:
    Grammar const& _grammar;         // Grammar.
    MarkedStream<Token> _marked;     // Input `Token` stream with markers.
    std::vector<Token> _tokens;      // Parsed tokens.
    std::vector<Node> _nodes;        // The DP array, aka. "shared packed parse forest (SPPF)".
    std::vector<IndexRange> _ranges; // Position -> index range of nodes at this position.
    ErrorRecoveryParams _params;     // Error recovery parameters.
    std::vector<Error> _errors;      // Logged errors.

    // Map for state deduplication: state -> node index.
    std::unordered_map<Node::State, size_t, Node::State::Hasher> _map;
    // Map of completion candidates: (end position, next symbol) -> node index.
    std::unordered_multimap<std::pair<size_t, Symbol>, size_t, PairHasher> _completions;
    // Map of null-completed nodes: (start and end position, symbol) -> node index.
    std::unordered_multimap<std::pair<size_t, Symbol>, size_t, PairHasher> _completed;

    auto _nextToken() -> std::optional<Token>;
    auto _skipTokens(size_t count) -> void;
    auto _node(size_t begin, size_t end, size_t rule, size_t progress) -> size_t;
    auto _transition(size_t prev, bool leaf, size_t child, size_t next) -> void;
    auto _run(bool initialCompletions = true, size_t length = std::numeric_limits<size_t>::max()) -> bool;
    auto _restore(size_t i) -> void;
  };

}

#endif // PARSING_PARSER_HPP_
