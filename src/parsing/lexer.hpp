#ifndef APIMU_PARSING_LEXER_HPP
#define APIMU_PARSING_LEXER_HPP

#include <array>
#include "stream.hpp"

namespace apimu::parsing {
#include "macros_open.hpp"

  // A class is a "string automaton" if...
  class Automaton {
    interface(Automaton);
  public:
    // It allows matching a prefix of a string, which:
    // Returns the matching pattern ID on success;
    // Returns `std::nullopt` on failure.
    virtual auto match(IStream<Char>& stream) const -> std::optional<Symbol> required;
  };

  // Nondeterministic finite automaton with ε-transitions.
  class NFA: public Automaton {
  public:
    struct Entry {
      std::vector<std::pair<Char, size_t>> outs; // List of out edges.
      std::optional<Symbol> mark;                // Is an accepting state?
    };
    std::vector<Entry> table; // The transition & accepting state table.
    size_t initial;           // The initial state.

    // Runs NFA.
    auto match(IStream<Char>& stream) const -> std::optional<Symbol> override;
  };

  // Deterministic finite automaton.
  class DFA: public Automaton {
  public:
    struct Entry {
      std::array<std::optional<size_t>, CharMax + 1> outs; // Char -> out edge (if present).
      std::optional<Symbol> mark;                          // Is an accepting state?
    };
    std::vector<Entry> table; // The transition & accepting state table.
    size_t initial;           // The initial state.

    // Runs DFA.
    auto match(IStream<Char>& stream) const -> std::optional<Symbol> override;
  };

  // Builds automata from regular expressions.
  class AutomatonBuilder {
  public:
    using Entry = NFA::Entry;
    using Subgraph = std::pair<size_t, size_t>;

    auto empty() -> Subgraph;
    auto any() -> Subgraph;
    auto utf8segment() -> Subgraph;
    auto chars(std::vector<Char> const& ls) -> Subgraph;
    auto except(std::vector<Char> const& ls) -> Subgraph;
    auto range(Char a, Char b) -> Subgraph;
    auto rangeExcept(Char a, Char b, std::vector<Char> const& ls) -> Subgraph;
    auto word(std::vector<Char> const& word) -> Subgraph;
    auto alt(std::vector<Subgraph> const& ls) -> Subgraph;
    auto concat(std::vector<Subgraph> const& ls) -> Subgraph;
    auto opt(Subgraph a) -> Subgraph;
    auto star(Subgraph a) -> Subgraph;
    auto plus(Subgraph a) -> Subgraph;

    // Registers a pattern constructed from functions above.
    // Input subgraph must be newly constructed in full. No "parts" can be reused.
    auto pattern(Symbol sym, Subgraph a) -> AutomatonBuilder&;

    // Constructs a well-formed NFA.
    auto makeNFA() const -> NFA;

    // Constructs a well-formed DFA, optionally minimised.
    auto makeDFA(bool minimise) const -> DFA;

  private:
    std::vector<Entry> _table; // The transition & accepting state table.
    size_t _initial = _node(); // The initial state.

    auto _node() -> size_t;
    auto _transition(size_t s, Char c, size_t t) -> void;
  };

  // A token emitted by a lexer.
  struct Token {
    std::optional<Symbol> id; // Terminal symbol ID (empty if unrecognised).
    std::string_view lexeme;  // Lexeme. `lexeme.size() == end - begin`.
    size_t begin;             // Start index in original character stream.
    size_t end;               // End index in original character stream.
  };

  // A lexer is a "revertable stream" of `Token`.
  class AutomatonLexer: public IMarkedStream<Token> {
  public:
    // Given references must be valid over the `Lexer`'s lifetime.
    AutomatonLexer(Automaton const& automaton, CharStream& stream):
      _automaton(automaton),
      _stream(stream),
      _offset(stream.position()) {}

    auto position() const -> size_t override { return _offsets.size(); }
    auto revert(size_t i) -> void override {
      assert(i <= _offsets.size());
      _offsets.resize(i);
      _stream.revert(_offsets.empty() ? _offset : _offsets.back());
    }
    auto mark() -> void override { _offsets.push_back(_stream.position()); }
    auto next() -> std::optional<Token> override;
    auto clear() -> void override { _offset = _stream.position(), _offsets.clear(); }

  private:
    Automaton const& _automaton;  // Underlying automaton.
    CharStream& _stream;          // Underlying stream.
    size_t _offset;               // Initial offset.
    std::vector<size_t> _offsets; // Offsets of marks.
  };

#include "macros_close.hpp"
}

#endif // APIMU_PARSING_LEXER_HPP
