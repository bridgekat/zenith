// Parsing :: Token, Lexer, NFALexer, DFALexer

#ifndef LEXER_HPP_
#define LEXER_HPP_

#include <array>
#include <concepts>
#include <optional>
#include <string>
#include <utility>
#include <vector>
#include <core/base.hpp>

namespace Parsing {

  struct Token {
    size_t pattern;
    size_t startPos;
    size_t endPos;
    std::string lexeme;
  };

  struct LexerError {
    size_t startPos;
    size_t endPos;
    std::string lexeme;
  };

  // Abstract base class for lexers.
  class Lexer {
  public:
    using CodeUnit = unsigned int;
    static constexpr CodeUnit SegBegin = 128u;
    static constexpr CodeUnit CodeUnits = 256u;

    virtual ~Lexer() = default;

    auto position() const -> size_t { return mPosition; }
    auto setPosition(size_t p) -> void { mPosition = p; }

    auto string() const -> std::string { return mString; }
    auto setString(std::string const& s) -> void { mPosition = 0, mString = s; }

    auto eof() const -> bool { return mPosition >= mString.size(); }
    auto nextToken() -> std::optional<Token>;
    auto popErrors() -> std::vector<LexerError> { return std::exchange(mErrors, {}); }

  protected:
    size_t mPosition;
    std::string mString;
    std::vector<LexerError> mErrors;

    Lexer():
      mPosition(0),
      mString(),
      mErrors(){};

    // Returns longest match in the form of (length, pattern ID).
    virtual auto run() const -> std::optional<std::pair<size_t, size_t>> = 0;
  };

  // Implementation based on NFA. Patterns can be added/removed after creation.
  class NFALexer: public Lexer {
  public:
    using State = size_t;
    using NFA = std::pair<State, State>;

    auto addPattern(NFA nfa) -> size_t {
      auto const id = patterns.size();
      patterns.push_back(nfa.first);
      auto& o = table[nfa.second].ac;
      if (o) unreachable;
      o = id;
      return id;
    }

    auto clearPatterns() -> void {
      table.clear();
      patterns.clear();
    }

    // Some useful pattern constructors (equivalent to regexes).
    auto empty() -> NFA {
      auto const s = node(), t = node();
      transition(s, 0, t);
      return {s, t};
    }
    auto any() -> NFA { return range(1, CodeUnits - 1); }
    auto utf8segment() -> NFA { return range(SegBegin, CodeUnits - 1); }
    auto chars(std::vector<CodeUnit> const& ls) -> NFA {
      auto const s = node(), t = node();
      for (auto const c: ls) transition(s, c, t);
      return {s, t};
    }
    auto except(std::vector<CodeUnit> const& ls) -> NFA {
      auto f = std::array<bool, CodeUnits>{};
      for (auto const c: ls) f[c] = true;
      auto const s = node(), t = node();
      for (auto i = 1u; i < CodeUnits; i++)
        if (!f[i]) transition(s, i, t);
      return {s, t};
    }
    auto range(CodeUnit a, CodeUnit b) -> NFA {
      auto const s = node(), t = node();
      for (auto i = a; i <= b; i++) transition(s, i, t);
      return {s, t};
    }
    auto word(std::vector<CodeUnit> const& word) -> NFA {
      auto const s = node();
      auto t = s;
      for (auto const c: word) {
        auto const curr = node();
        transition(t, c, curr);
        t = curr;
      }
      return {s, t};
    }
    auto alt(std::vector<NFA> const& ls) -> NFA {
      auto const s = node(), t = node();
      for (auto const& a: ls) {
        transition(s, 0, a.first);
        transition(a.second, 0, t);
      }
      return {s, t};
    }
    auto concat(std::vector<NFA> const& ls) -> NFA {
      if (ls.empty()) unreachable;
      for (auto i = 0uz; i + 1 < ls.size(); i++) {
        auto const a = ls[i], b = ls[i + 1];
        for (auto const& [c, t]: table[b.first].tr) transition(a.second, c, t);
      }
      return {ls.front().first, ls.back().second};
    }
    auto opt(NFA const& a) -> NFA {
      transition(a.first, 0, a.second);
      return {a.first, a.second};
    }
    auto star(NFA const& a) -> NFA {
      auto const s = node(), t = node();
      transition(s, 0, a.first);
      transition(a.second, 0, t);
      transition(a.second, 0, a.first);
      transition(s, 0, t);
      return {s, t};
    }
    auto plus(NFA const& a) -> NFA { return concat({a, star(a)}); }

    // Returns the size of the table.
    auto tableSize() const -> size_t { return table.size(); }

  private:
    class Entry {
    public:
      std::vector<std::pair<CodeUnit, State>> tr;
      std::optional<size_t> ac;
    };

    std::vector<Entry> table;    // The transition & accepting state table.
    std::vector<State> patterns; // The list of starting states, one for each pattern.

    // Allocates new node and returns its ID.
    auto node() -> size_t {
      auto const res = table.size();
      table.emplace_back();
      return res;
    }

    // Adds a transition from node `s` to node `t` with character `c`.
    auto transition(State s, CodeUnit c, State t) -> void { table[s].tr.emplace_back(c, t); }

    // Expands `s` to epsilon closure using DFS.
    // Pre: the indices where `v[]` is true must match the elements of `s`.
    auto closure(std::vector<bool>& v, std::vector<State>& s) const -> void;

    // Directly runs NFA.
    auto run() const -> std::optional<std::pair<size_t, size_t>> override;

    // Function object for the DFA construction from NFA.
    friend class PowersetConstruction;
  };

  // Implementation based on DFA. Could only be constructed from an `NFALexer`.
  class DFALexer: public Lexer {
  public:
    using State = size_t;

    // Constructs DFA from NFA using `PowersetConstruction`.
    explicit DFALexer(NFALexer const& nfa);

    // Minimises DFA.
    auto minimise() -> void;

    // Returns the size of the table.
    auto tableSize() const -> size_t { return table.size(); }

  private:
    class Entry {
    public:
      std::array<bool, CodeUnits> has{};
      std::array<State, CodeUnits> tr{};
      std::optional<size_t> ac;
    };

    std::vector<Entry> table; // The transition & accepting state table.
    State initial = 0;        // The initial state.

    // Runs DFA.
    auto run() const -> std::optional<std::pair<size_t, size_t>> override;

    // Function object for the DFA construction from NFA.
    friend class PowersetConstruction;

    // Function object for the DFA state minimisation.
    friend class PartitionRefinement;
  };

}

#endif // LEXER_HPP_
