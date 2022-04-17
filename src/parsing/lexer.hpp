// Parsing :: Symbol, ParseTree, Lexer, NFALexer, DFALexer

#ifndef LEXER_HPP_
#define LEXER_HPP_

#include <vector>
#include <array>
#include <utility>
#include <optional>
#include <string>
#include <limits>
#include <core/base.hpp>


namespace Parsing {

  using std::vector;
  using std::array;
  using std::pair, std::make_pair;
  using std::optional, std::make_optional, std::nullopt;
  using std::string;


  // Symbol ID (Lean name: "syntactic category")
  using Symbol = size_t;

  // Parse tree node, also used as tokens (Lean name: "syntax")
  struct ParseTree {
    ParseTree* s, * c;
    Symbol id;
    optional<string> lexeme;       // Terminal symbols only
    optional<size_t> patternIndex; // Terminal symbols only
    optional<size_t> ruleIndex;    // Nonterminal symbols only
    size_t startPos, endPos;       // Measured in characters: [startPos, endPos)
  };

  // A common (abstract) base class for lexers.
  class Lexer {
  public:
    // See: https://stackoverflow.com/questions/39646958/constexpr-static-member-before-after-c17
    static constexpr unsigned int SegBegin = 128;
    static constexpr unsigned int CodeUnits = 256;
    static_assert(CodeUnits == static_cast<unsigned int>(std::numeric_limits<char8_t>::max()) + 1);

    struct ErrorInfo {
      size_t startPos, endPos;
      string lexeme;
      ErrorInfo(size_t startPos, size_t endPos, std::string lexeme):
        startPos(startPos), endPos(endPos), lexeme(std::move(lexeme)) {}
    };

    virtual ~Lexer() = default;

    bool eof() const noexcept { return pos >= str.size(); }
    size_t position() const noexcept { return pos; }
    void setPosition(size_t p) noexcept { pos = p; }
    void setString(const string& s) { pos = 0; str = s; }

    // All errors will be logged
    optional<ParseTree> nextToken();
    // Get and clear error log
    vector<ErrorInfo> popErrors();
    // Returns the corresponding symbol ID for a given pattern ID
    virtual Symbol patternSymbol(size_t id) const = 0;

  protected:
    size_t pos;
    string str;
    vector<ErrorInfo> errors;

    Lexer(): pos(0), str(), errors() {};

    // Returns longest match in the form of (length, pattern ID)
    virtual optional<pair<size_t, size_t>> run() const = 0;
  };

  // Implementation based on NFA. You may add patterns after construction.
  class NFALexer: public Lexer {
  public:
    using State = size_t;
    using NFA = pair<State, State>;

    NFALexer(): Lexer(), table(), patterns() {}

    // Add pattern (mark accepting state)
    // Returns pattern ID
    size_t addPattern(Symbol sym, NFA nfa) {
      size_t id = patterns.size();
      auto& o = table[nfa.second].ac;
      if (o) unreachable;
      o = id;
      // patterns.emplace_back(nfa.first, sym, true);
      patterns.push_back(Pattern{ nfa.first, sym, true });
      return id;
    }

    // Returns true if pattern was previously active
    // Other pattern IDs are unaffected
    bool removePattern(size_t id) {
      if (id >= patterns.size()) unreachable;
      if (!patterns[id].active) return false;
      patterns[id].active = false;
      return true;
    }

    Symbol patternSymbol(size_t id) const override {
      return patterns[id].symbol;
    }

    #define node(x) State x = table.size(); table.emplace_back()
    #define trans(s, c, t) table[s].tr.emplace_back(static_cast<char8_t>(c), t)

    // Some useful pattern constructors (equivalent to regexes)
    NFA epsilon() {
      node(s); node(t); trans(s, 0, t);
      return { s, t };
    }
    NFA ch_vec(const vector<char8_t>& ls) {
      node(s); node(t);
      for (auto c: ls) trans(s, c, t);
      return { s, t };
    }
    template <typename... Ts>
    NFA ch(Ts... a) { return ch_vec({ static_cast<char8_t>(a)... }); }
    NFA range(char8_t a, char8_t b) {
      node(s); node(t);
      for (unsigned int i = a; i <= b; i++) trans(s, i, t);
      return { s, t };
    }
    NFA concat2(NFA a, NFA b) {
      for (auto [c, t]: table[b.first].tr) trans(a.second, c, t);
      return { a.first, b.second };
    }
    template <typename... Ts>
    NFA concat(NFA a, Ts... b) { return concat2(a, concat(b...)); }
    NFA concat(NFA a) { return a; }
    NFA word(const string& word) {
      node(s); State t = s;
      for (char8_t c: word) {
        node(curr);
        trans(t, c, curr);
        t = curr;
      }
      return { s, t };
    }
    NFA alt_vec(const vector<NFA>& ls) {
      node(s); node(t);
      for (auto a: ls) {
        trans(s, 0, a.first);
        trans(a.second, 0, t);
      }
      return { s, t };
    }
    template <typename... Ts>
    NFA alt(Ts... a) { return alt_vec({ a... }); }
    NFA star(NFA a) {
      node(s); node(t);
      trans(s, 0, a.first); trans(a.second, 0, t);
      trans(a.second, 0, a.first); trans(s, 0, t);
      return { s, t };
    }
    NFA opt(NFA a) {
      trans(a.first, 0, a.second);
      return { a.first, a.second };
    }
    NFA plus(NFA a)   { return concat2(a, star(a)); }
    NFA any()         { return range(1, CodeUnits - 1); }
    NFA utf8segment() { return range(SegBegin, CodeUnits - 1); }
    NFA except_vec(const vector<char8_t>& ls) {
      array<bool, CodeUnits> f{};
      for (auto c: ls) f[c] = true;
      node(s); node(t);
      for (unsigned int i = 1; i < CodeUnits; i++) if (!f[i]) trans(s, i, t);
      return { s, t };
    }
    template <typename... Ts>
    NFA except(Ts... a) { return except_vec({ static_cast<char8_t>(a)... }); }

    #undef node
    #undef trans

    // Returns the size of the table
    size_t tableSize() const noexcept { return table.size(); }

  private:
    // The transition & accepting state table
    struct Entry {
      vector<pair<char8_t, State>> tr;
      optional<size_t> ac;
      Entry(): tr(), ac() {}
    };
    vector<Entry> table;
    // The list of patterns
    struct Pattern {
      State initial;
      Symbol symbol;
      bool active;
    };
    vector<Pattern> patterns;

    optional<pair<size_t, size_t>> run() const override;

    friend class PowersetConstruction;
  };

  // Implementation based on DFA. Could only be constructed from an `NFALexer`.
  class DFALexer: public Lexer {
  public:
    using State = size_t;

    // Create DFA from NFA
    explicit DFALexer(const NFALexer& nfa);

    Symbol patternSymbol(size_t id) const override {
      return patternSymbols[id];
    }

    // Optimize DFA
    void optimize();

    // Returns the size of the table
    size_t tableSize() const noexcept { return table.size(); }

    // Convert lexer DFA to TextMate grammar JSON (based on regular expressions)
    // Following: https://macromates.com/manual/en/regular_expressions (only a simple subset is used)
    // (Not implemented)
    string toTextMateGrammar() const;

  private:
    // The transition & accepting state table
    struct Entry {
      array<bool, CodeUnits> has;
      array<State, CodeUnits> tr;
      optional<size_t> ac;
      Entry(): has{}, tr{}, ac() {}
    };
    vector<Entry> table;
    // The initial state
    State initial;
    // Mapping from pattern ID to symbol ID
    vector<Symbol> patternSymbols;

    optional<pair<size_t, size_t>> run() const override;

    friend class PowersetConstruction;
    friend class PartitionRefinement;
  };

}

#endif // LEXER_HPP_
