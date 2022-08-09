// Parsing :: Token, Lexer, NFALexer, DFALexer

#ifndef LEXER_HPP_
#define LEXER_HPP_

#include <array>
#include <optional>
#include <string>
#include <utility>
#include <vector>
#include <core/base.hpp>

namespace Parsing {

  using std::vector;
  using std::array;
  using std::pair, std::make_pair;
  using std::optional, std::make_optional, std::nullopt;
  using std::string;

  struct Token {
    size_t pattern, startPos, endPos;
    string lexeme;
  };

  // A common (abstract) base class for lexers.
  class Lexer {
  public:
    struct ErrorInfo {
      size_t startPos, endPos;
      string lexeme;
    };
    static constexpr unsigned int SegBegin = 128;
    static constexpr unsigned int CodeUnits = 256;

    virtual ~Lexer() = default;

    bool eof() const noexcept { return pos >= str.size(); }
    size_t position() const noexcept { return pos; }
    void setPosition(size_t p) noexcept { pos = p; }
    void setString(const string& s) { pos = 0, str = s; }

    optional<Token> nextToken();
    vector<ErrorInfo> popErrors() { return std::exchange(errors, {}); }

  protected:
    size_t pos;
    string str;
    vector<ErrorInfo> errors;

    Lexer(): pos(0), str(), errors(){};

    // Returns longest match in the form of (length, pattern ID)
    virtual optional<pair<size_t, size_t>> run() const = 0;
  };

  // Implementation based on NFA. Patterns can be added/removed after creation.
  class NFALexer: public Lexer {
  public:
    using State = size_t;
    using NFA = pair<State, State>;

    NFALexer(): Lexer(), table(), patterns() {}

    size_t addPattern(NFA nfa) {
      size_t id = patterns.size();
      patterns.push_back(nfa.first);
      auto& o = table[nfa.second].ac;
      if (o) unreachable;
      o = id;
      return id;
    }

    void clearPatterns() noexcept {
      table.clear();
      patterns.clear();
    }

#define node(x)           \
  State x = table.size(); \
  table.emplace_back()
#define trans(s, c, t) table[s].tr.emplace_back(static_cast<char8_t>(c), t)

    // Some useful pattern constructors (equivalent to regexes)
    NFA empty() {
      node(s);
      node(t);
      trans(s, 0, t);
      return {s, t};
    }
    NFA any() { return range(1, CodeUnits - 1); }
    NFA utf8segment() { return range(SegBegin, CodeUnits - 1); }

    template <typename... Ts>
    NFA chars(Ts... a) {
      return charsvec({static_cast<char8_t>(a)...});
    }
    NFA charsvec(const vector<char8_t>& ls) {
      node(s);
      node(t);
      for (auto c: ls) trans(s, c, t);
      return {s, t};
    }

    template <typename... Ts>
    NFA except(Ts... a) {
      return exceptvec({static_cast<char8_t>(a)...});
    }
    NFA exceptvec(const vector<char8_t>& ls) {
      array<bool, CodeUnits> f{};
      for (auto c: ls) f[c] = true;
      node(s);
      node(t);
      for (unsigned int i = 1; i < CodeUnits; i++)
        if (!f[i]) trans(s, i, t);
      return {s, t};
    }

    NFA range(char8_t a, char8_t b) {
      node(s);
      node(t);
      for (unsigned int i = a; i <= b; i++) trans(s, i, t);
      return {s, t};
    }
    NFA word(const vector<char8_t>& word) {
      node(s);
      State t = s;
      for (char8_t c: word) {
        node(curr);
        trans(t, c, curr);
        t = curr;
      }
      return {s, t};
    }

    template <typename... Ts>
    NFA alt(Ts... a) {
      return altvec({a...});
    }
    NFA altvec(const vector<NFA>& ls) {
      node(s);
      node(t);
      for (auto a: ls) {
        trans(s, 0, a.first);
        trans(a.second, 0, t);
      }
      return {s, t};
    }

    template <typename... Ts>
    NFA concat(Ts... a) {
      return concatvec({a...});
    }
    NFA concatvec(const vector<NFA>& ls) {
      if (ls.empty()) unreachable;
      for (size_t i = 0; i + 1 < ls.size(); i++) {
        auto a = ls[i], b = ls[i + 1];
        for (auto [c, t]: table[b.first].tr) trans(a.second, c, t);
      }
      return {ls.front().first, ls.back().second};
    }

    NFA opt(NFA a) {
      trans(a.first, 0, a.second);
      return {a.first, a.second};
    }
    NFA star(NFA a) {
      node(s);
      node(t);
      trans(s, 0, a.first);
      trans(a.second, 0, t);
      trans(a.second, 0, a.first);
      trans(s, 0, t);
      return {s, t};
    }
    NFA plus(NFA a) { return concat(a, star(a)); }

#undef node
#undef trans

    // Returns the size of the table
    size_t tableSize() const noexcept { return table.size(); }

  private:
    struct Entry {
      vector<pair<char8_t, State>> tr;
      optional<size_t> ac;
      Entry(): tr(), ac() {}
    };
    vector<Entry> table;    // The transition & accepting state table
    vector<State> patterns; // The list of starting states, one for each pattern

    optional<pair<size_t, size_t>> run() const override;

    friend class PowersetConstruction;
  };

  // Implementation based on DFA. Could only be constructed from an `NFALexer`.
  class DFALexer: public Lexer {
  public:
    using State = size_t;

    // Create DFA from NFA
    explicit DFALexer(const NFALexer& nfa);

    // Optimize DFA
    void optimize();

    // Returns the size of the table
    size_t tableSize() const noexcept { return table.size(); }

  private:
    struct Entry {
      array<bool, CodeUnits> has;
      array<State, CodeUnits> tr;
      optional<size_t> ac;
      Entry(): has{}, tr{}, ac() {}
    };
    vector<Entry> table; // The transition & accepting state table
    State initial;       // The initial state

    optional<pair<size_t, size_t>> run() const override;

    friend class PowersetConstruction;
    friend class PartitionRefinement;
  };

}

#endif // LEXER_HPP_
