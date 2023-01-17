// Parsing :: Automaton, NFA, DFA, Lexer

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
  public:
    virtual ~Automaton() {}
    // It allows matching a prefix of a string, which:
    // Returns the matching pattern ID and advances `string` on success;
    // Returns `std::nullopt` and leaves `string` in its original position on failure.
    virtual auto match(Generator<Char>& string) const -> std::optional<Symbol> pure_virtual;
  };

  // TODO: make a builder class.
  class NFA: public Automaton {
  public:
    struct Entry {
      std::vector<std::pair<Char, size_t>> outs; // List of out edges.
      std::optional<Symbol> mark;                // Is an accepting state?
    };
    using Subgraph = std::pair<size_t, size_t>;

    // Returns a const reference to the table.
    auto table() const -> std::vector<Entry> const& { return mTable; }

    // Returns initial state ID.
    auto initial() const -> size_t { return mInitial; }

    // Some useful pattern constructors (equivalent to regexes).
    auto empty() -> Subgraph {
      auto const s = node(), t = node();
      transition(s, 0, t);
      return {s, t};
    }
    auto any() -> Subgraph { return range(1, CharMax); }
    auto utf8segment() -> Subgraph { return range(128, CharMax); }
    auto chars(std::vector<Char> const& ls) -> Subgraph {
      auto const s = node(), t = node();
      for (auto const c: ls) transition(s, c, t);
      return {s, t};
    }
    auto except(std::vector<Char> const& ls) -> Subgraph {
      auto f = std::array<bool, CharMax + 1>{};
      for (auto const c: ls) f[c] = true;
      auto const s = node(), t = node();
      for (auto i = 1_z; i <= CharMax; i++)
        if (!f[i]) transition(s, i, t);
      return {s, t};
    }
    auto range(Char a, Char b) -> Subgraph {
      auto const s = node(), t = node();
      for (auto i = size_t{a}; i <= size_t{b}; i++) transition(s, i, t);
      return {s, t};
    }
    auto word(std::vector<Char> const& word) -> Subgraph {
      auto const s = node();
      auto t = s;
      for (auto const c: word) {
        auto const curr = node();
        transition(t, c, curr);
        t = curr;
      }
      return {s, t};
    }
    auto alt(std::vector<Subgraph> const& ls) -> Subgraph {
      auto const s = node(), t = node();
      for (auto const& a: ls) {
        transition(s, 0, a.first);
        transition(a.second, 0, t);
      }
      return {s, t};
    }
    auto concat(std::vector<Subgraph> const& ls) -> Subgraph {
      assert_always(!ls.empty());
      for (auto i = 0_z; i + 1 < ls.size(); i++) {
        auto const a = ls[i], b = ls[i + 1];
        for (auto const& [c, t]: mTable[b.first].outs) transition(a.second, c, t);
      }
      return {ls.front().first, ls.back().second};
    }
    auto opt(Subgraph a) -> Subgraph {
      transition(a.first, 0, a.second);
      return {a.first, a.second};
    }
    auto star(Subgraph a) -> Subgraph {
      auto const s = node(), t = node();
      transition(s, 0, a.first);
      transition(a.second, 0, t);
      transition(a.second, 0, a.first);
      transition(s, 0, t);
      return {s, t};
    }
    auto plus(Subgraph a) -> Subgraph { return concat({a, star(a)}); }

    // Registers a pattern constructed from functions above.
    // Input subgraph must be newly constructed in full. No "parts" can be reused.
    auto addPattern(Symbol sym, Subgraph a) -> void {
      transition(mInitial, 0, a.first);
      mTable[a.second].mark = sym;
    }

    // Clears everything.
    auto clear() -> void {
      mTable.clear();
      mInitial = node();
    }

  private:
    std::vector<Entry> mTable; // The transition & accepting state table.
    size_t mInitial = node();  // The initial state.

    // Allocates new node and returns its ID.
    auto node() -> size_t {
      auto const res = mTable.size();
      mTable.emplace_back();
      return res;
    }

    // Adds a transition from node `s` to node `t` with character `c`.
    auto transition(size_t s, size_t c, size_t t) -> void { mTable[s].outs.emplace_back(c, t); }

    // Expands `s` to ε-closure using DFS.
    // Pre: the indices where `v[]` is true must match the elements of `s`.
    auto closure(std::vector<bool>& v, std::vector<size_t>& s) const -> void;

    // Directly runs NFA.
    auto match(Generator<Char>& string) const -> std::optional<Symbol> override;

    friend class PowersetConstruction;
  };

  class DFA: public Automaton {
  public:
    struct Entry {
      std::array<std::optional<size_t>, CharMax + 1> outs; // Char -> out edge (if valid).
      std::optional<Symbol> mark;                          // Is an accepting state?
    };

    // Constructs DFA from NFA using powerset construction.
    explicit DFA(NFA const& nfa);

    // Returns a const reference to the table.
    auto table() const -> std::vector<Entry> const& { return mTable; }

    // Returns initial state ID.
    auto initial() const -> size_t { return mInitial; }

    // Minimises DFA.
    auto minimise() -> void;

  private:
    std::vector<Entry> mTable; // The transition & accepting state table.
    size_t mInitial;           // The initial state.

    // Allocates new node and returns its ID.
    auto node() -> size_t {
      auto const res = mTable.size();
      mTable.emplace_back();
      return res;
    }

    // Adds a transition from node `s` to node `t` with character `c`.
    auto transition(size_t s, size_t c, size_t t) -> void { mTable[s].outs[c] = t; }

    // Runs DFA.
    auto match(Generator<Char>& string) const -> std::optional<Symbol> override;

    friend class PowersetConstruction;
    friend class PartitionRefinement;
  };

  // A lexer is a "revertable generator" of `std::optional<Token>`.
  // It generates the next token if a prefix match is found,
  // or `std::nullopt` (and skips a single UTF-8 code point) in case of a failed match.
  class Lexer: public Generator<std::optional<Token>> {
  public:
    Lexer(Automaton const* automaton, CharBuffer* string):
      mAutomaton(automaton),
      mString(string) {}

    auto eof() const -> bool override { return mString->eof(); }
    auto advance() -> std::optional<Token> override;
    auto position() const -> size_t override { return mPositions.size(); }
    auto revert(size_t i) -> void override {
      assert_always(i <= mPositions.size());
      mPositions.resize(i);
      mString->revert(mPositions.empty() ? 0 : mPositions.back());
    }

  private:
    Automaton const* mAutomaton;    // Underlying automaton.
    CharBuffer* mString;            // Input `Char` stream.
    std::vector<size_t> mPositions; // End positions in the input `Char` stream.
  };

}

#endif // LEXER_HPP_
