#ifndef APIMU_PARSING_PARSER_HPP
#define APIMU_PARSING_PARSER_HPP

#include <unordered_map>
#include "lexer.hpp"
#include "stream.hpp"

namespace apimu::parsing {
#include "macros_open.hpp"

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
    // Pair of (symbol ID, precedence) with convenient constructors.
    struct InputPair {
      std::pair<Symbol, Precedence> value;
      constexpr InputPair(Symbol symbol, Precedence precedence = PrecedenceMax):
        value(symbol, precedence) {}
    };

    auto start(Symbol value) -> GrammarBuilder&;
    auto ignored(Symbol value) -> GrammarBuilder&;
    auto rule(InputPair lhs, std::vector<InputPair> const& rhs) -> GrammarBuilder&;

    // Constructs a well-formed `Grammar`.
    auto makeGrammar() const -> Grammar;

  private:
    Symbol _startSymbol = 0;
    Symbol _ignoredSymbol = 0;
    std::vector<Grammar::Rule> _rules;
  };

  // A left-match SPPF node emitted by a parser.
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
    std::vector<Link> next; // Forward links (temporary).
    std::vector<Link> prev; // Backward links.
  };

  // Error recovery parameters.
  struct ErrorRecoveryParams {
    bool rollback = false; // Try rolling back to last successful position before error recovery.
    size_t maxSkipped = 4; // Max number of skipped tokens around an error.
    size_t threshold = 4;  // Number of tokens to be recognised before declaring success.
  };

  // Error handler interface.
  class IErrorHandler {
    interface(IErrorHandler);
  public:
    // Params: expected symbol IDs (terminals and nonterminals), problematic token (empty if reached EOF).
    virtual auto parsingError(std::vector<Symbol> expected, std::optional<Token> got) -> void required;
  };

  // An "error handler" that does nothing on error.
  class BasicErrorHandler: public IErrorHandler {
  public:
    auto parsingError(std::vector<Symbol>, std::optional<Token>) -> void override {}
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

    // Given references must be valid over the `Parser`'s lifetime.
    EarleyParser(Grammar const& grammar, IStream<Token>& stream, ErrorRecoveryParams params, IErrorHandler& handler):
      _grammar(grammar),
      _marked(stream),
      _params(std::move(params)),
      _handler(handler) {}

    // Parse with error recovery.
    // Returns true if no error is detected (and the parse forest is complete).
    auto parse() -> bool;

    // Retrieves results.
    auto grammar() const -> Grammar const& { return _grammar; }
    auto tokens() const -> std::vector<Token> const& { return _tokens; }
    auto nodes() const -> std::vector<Node> const& { return _nodes; }
    auto ranges() const -> std::vector<IndexRange> const& { return _ranges; }
    auto finalStates(std::optional<size_t> optPosition = {}) const -> std::vector<size_t>;

    // Temporarily constructs forward links for unvisited nodes. Useful in disambiguation stage.
    auto propagate(std::vector<size_t> stk) -> size_t;
    auto unpropagate(std::vector<size_t> stk) -> void;

  private:
    Grammar const& _grammar;           // Grammar.
    MarkedStream<Token> _marked;       // Input `Token` stream with markers.
    std::vector<Token> _tokens;        // Parsed tokens.
    std::vector<Node> _nodes;          // The DP array, aka. "shared packed parse forest (SPPF)".
    std::vector<IndexRange> _ranges;   // Position -> index range of nodes at this position.
    ErrorRecoveryParams const _params; // Error recovery parameters.
    IErrorHandler& _handler;           // Error handler.

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
    enum class Result { eofSuccess, eofFailure, emptyFailure, reachedLength };
    auto _run(bool recoveryMode, std::optional<size_t> optLength = {}) -> Result;
    auto _restore(size_t i) -> void;
  };

#include "macros_close.hpp"
}

#endif // APIMU_PARSING_PARSER_HPP
