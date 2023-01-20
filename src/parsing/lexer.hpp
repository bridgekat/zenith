// Parsing :: Automaton, AutomatonBuilder, Token, Lexer...

#ifndef LEXER_HPP_
#define LEXER_HPP_

#include <array>
#include <optional>
#include <utility>
#include <vector>
#include <common.hpp>
#include "generator.hpp"

namespace Parsing {

  // A class is a "string automaton" if...
  class Automaton {
    interface(Automaton);
  public:
    // It allows matching a prefix of a string, which:
    // Returns the matching pattern ID and advances `string` on success;
    // Returns `std::nullopt` and leaves `string` in its original position on failure.
    virtual auto match(Generator<Char>& string) const -> std::optional<Symbol> required;
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
    auto match(Generator<Char>& string) const -> std::optional<Symbol> override;
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
    auto match(Generator<Char>& string) const -> std::optional<Symbol> override;
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
    auto word(std::vector<Char> const& word) -> Subgraph;
    auto alt(std::vector<Subgraph> const& ls) -> Subgraph;
    auto concat(std::vector<Subgraph> const& ls) -> Subgraph;
    auto opt(Subgraph a) -> Subgraph;
    auto star(Subgraph a) -> Subgraph;
    auto plus(Subgraph a) -> Subgraph;

    // Registers a pattern constructed from functions above.
    // Input subgraph must be newly constructed in full. No "parts" can be reused.
    auto withPattern(Symbol sym, Subgraph a) -> AutomatonBuilder&;

    // Constructs a well-formed NFA.
    auto makeNFA() -> NFA const;

    // Constructs a well-formed DFA, optionally minimised.
    auto makeDFA(bool minimise) -> DFA const;

  private:
    std::vector<Entry> _table; // The transition & accepting state table.
    size_t _initial = _node(); // The initial state.

    auto _node() -> size_t;
    auto _transition(size_t s, Char c, size_t t) -> void;
  };

  // A token emitted by a lexer.
  struct Token {
    Symbol id;               // Terminal symbol ID.
    size_t begin;            // Start index in original string.
    size_t end;              // End index in original string.
    std::string_view lexeme; // Lexeme. `lexeme.size() == end - begin`.
  };

  // A lexer is a "revertable generator" of `std::optional<Token>`.
  // It generates the next token if a prefix match is found,
  // or `std::nullopt` (and skips a single UTF-8 code point) in case of a failed match.
  class Lexer: public Generator<std::optional<Token>> {
  public:
    // Given references must be valid over the `Lexer`'s lifetime.
    Lexer(Automaton const& automaton, CharBuffer& string):
      _automaton(automaton),
      _string(string),
      _offset(string.position()) {}

    auto eof() const -> bool override { return _string.eof(); }
    auto advance() -> std::optional<Token> override;
    auto position() const -> size_t override { return _offsets.size(); }
    auto revert(size_t i) -> void override {
      assert(i <= _offsets.size());
      _offsets.resize(i);
      _string.revert(_offsets.empty() ? _offset : _offsets.back());
    }

  private:
    Automaton const& _automaton;  // Underlying automaton.
    CharBuffer& _string;          // Input `Char` stream.
    size_t _offset;               // Starting position in the input `Char` stream.
    std::vector<size_t> _offsets; // End positions in the input `Char` stream.
  };
}

#endif // LEXER_HPP_
