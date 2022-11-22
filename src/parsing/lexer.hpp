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
    static constexpr auto SegBegin = 128u;
    static constexpr auto CodeUnits = 256u;

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
      auto id = patterns.size();
      patterns.push_back(nfa.first);
      auto& o = table[nfa.second].ac;
      if (o) unreachable;
      o = id;
      return id;
    }

    void clearPatterns() {
      table.clear();
      patterns.clear();
    }

#define node(x)           \
  State x = table.size(); \
  table.emplace_back()
#define trans(s, c, t) table[s].tr.emplace_back(static_cast<char8_t>(c), t)

    // Some useful pattern constructors (equivalent to regexes).
    auto empty() -> NFA {
      node(s);
      node(t);
      trans(s, 0, t);
      return {s, t};
    }
    auto any() -> NFA { return range(1, CodeUnits - 1); }
    auto utf8segment() -> NFA { return range(SegBegin, CodeUnits - 1); }
    auto chars(std::vector<char8_t> const& ls) -> NFA {
      node(s);
      node(t);
      for (auto c: ls) trans(s, c, t);
      return {s, t};
    }
    auto except(std::vector<char8_t> const& ls) -> NFA {
      std::array<bool, CodeUnits> f{};
      for (auto c: ls) f[c] = true;
      node(s);
      node(t);
      for (unsigned int i = 1; i < CodeUnits; i++)
        if (!f[i]) trans(s, i, t);
      return {s, t};
    }
    auto range(char8_t a, char8_t b) -> NFA {
      node(s);
      node(t);
      for (unsigned int i = a; i <= b; i++) trans(s, i, t);
      return {s, t};
    }
    auto word(std::vector<char8_t> const& word) -> NFA {
      node(s);
      State t = s;
      for (char8_t c: word) {
        node(curr);
        trans(t, c, curr);
        t = curr;
      }
      return {s, t};
    }
    auto alt(std::vector<NFA> const& ls) -> NFA {
      node(s);
      node(t);
      for (auto a: ls) {
        trans(s, 0, a.first);
        trans(a.second, 0, t);
      }
      return {s, t};
    }
    auto concat(std::vector<NFA> const& ls) -> NFA {
      if (ls.empty()) unreachable;
      for (size_t i = 0; i + 1 < ls.size(); i++) {
        auto a = ls[i], b = ls[i + 1];
        for (auto [c, t]: table[b.first].tr) trans(a.second, c, t);
      }
      return {ls.front().first, ls.back().second};
    }
    auto opt(NFA const& a) -> NFA {
      trans(a.first, 0, a.second);
      return {a.first, a.second};
    }
    auto star(NFA const& a) -> NFA {
      node(s);
      node(t);
      trans(s, 0, a.first);
      trans(a.second, 0, t);
      trans(a.second, 0, a.first);
      trans(s, 0, t);
      return {s, t};
    }
    auto plus(NFA const& a) -> NFA { return concat({a, star(a)}); }

#undef node
#undef trans

    // Returns the size of the table.
    auto tableSize() const -> size_t { return table.size(); }

  private:
    class Entry {
    public:
      std::vector<std::pair<char8_t, State>> tr;
      std::optional<size_t> ac;
    };

    std::vector<Entry> table;    // The transition & accepting state table.
    std::vector<State> patterns; // The list of starting states, one for each pattern.

    // Expands `s` to epsilon closure using DFS.
    // Pre: the indices where v[] is true must match the elements of s.
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
