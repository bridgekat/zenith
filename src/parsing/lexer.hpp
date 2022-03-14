// Parsing :: Token, TokenID, NFALexer, DFALexer

#ifndef LEXER_HPP_
#define LEXER_HPP_

#include <initializer_list>
#include <vector>
#include <algorithm>
#include <optional>
#include <compare>
#include <string>


namespace Parsing {

  using std::initializer_list;
  using std::vector;
  using std::pair, std::make_pair;
  using std::optional, std::make_optional, std::nullopt;
  using std::string;


  typedef unsigned int TokenID;
  struct Token {
    TokenID id;
    size_t startPos, endPos;
    string lexeme;
    std::strong_ordering operator<=>(const Token&) const = default;
  };

  // A common (abstract) base class for lexers.
  class Lexer {
  public:
    virtual ~Lexer() = default;
    virtual optional<pair<size_t, TokenID>> run(const string& s) const = 0;

    void setRest(const string& s) { pos = 0; rest = s; }
    Lexer& operator<<(const string& s) { rest += s; return *this; }

    const string& getRest() const noexcept { return rest; }
    bool eof() const noexcept { return rest.empty(); }

    optional<Token> getNextToken();
    void ignoreNextCodepoint();

  protected:
    size_t pos;
    string rest;

    Lexer(): pos(0), rest() {};
  };

  // Implementation based on NFA. You may add patterns after construction.
  class NFALexer: public Lexer {
  public:
    typedef unsigned int State;
    typedef pair<State, State> NFA;

    // Create initial state
    NFALexer(): Lexer(), table(), initial(0) { table.emplace_back(); }

    #define node(x) State x = table.size(); table.emplace_back()
    #define trans(s, c, t) table[s].tr.emplace_back(c, t)

    // Add pattern (mark accepting state)
    void addPattern(TokenID id, NFA nfa) {
      trans(initial, 0, nfa.first);
      auto& o = table[nfa.second].ac;
      if (!o.has_value()) o = id;
    }

    // Returns longest match in the form of (length, token)
    optional<pair<size_t, TokenID>> run(const string& s) const override;

    // Some useful pattern constructors (equivalent to regexes)
    NFA epsilon() {
      node(s); node(t); trans(s, 0, t);
      return { s, t };
    }
    NFA ch(const initializer_list<unsigned char>& ls) {
      node(s); node(t);
      for (auto c: ls) trans(s, c, t);
      return { s, t };
    }
    NFA range(unsigned char a, unsigned char b) {
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
    NFA word(const string& str) {
      node(s); State t = s;
      for (unsigned char c: str) {
        node(curr);
        trans(t, c, curr);
        t = curr;
      }
      return { s, t };
    }
    NFA alt(const initializer_list<NFA>& ls) {
      node(s); node(t);
      for (auto a: ls) {
        trans(s, 0, a.first);
        trans(a.second, 0, t);
      }
      return { s, t };
    }
    NFA star(NFA a) {
      node(s); node(t);
      trans(s, 0, a.first); trans(a.second, 0, t);
      trans(a.second, 0, a.first); trans(s, 0, t);
      return { s, t };
    }
    NFA plus(NFA a)   { return concat2(a, star(a)); }
    NFA any()         { return range(0x01, 0xFF); }
    NFA utf8segment() { return range(0x80, 0xFF); }
    NFA except(const initializer_list<unsigned char>& ls) {
      vector<bool> f(0x100, true);
      for (auto c: ls) f[c] = false;
      node(s); node(t);
      for (unsigned int i = 0x01; i <= 0xFF; i++) if (f[i]) trans(s, i, t);
      return { s, t };
    }

    #undef node
    #undef trans

    size_t size() { return table.size(); }

  private:
    // The transition & accepting state table
    struct Entry {
      vector<pair<unsigned char, State>> tr;
      optional<TokenID> ac;
      Entry(): tr(), ac() {}
    };
    vector<Entry> table;

    // The initial state
    State initial;

    friend class PowersetConstruction;
  };

  // Implementation based on DFA. Could only be constructed from an `NFALexer`.
  class DFALexer: public Lexer {
  public:
    typedef unsigned int State;

    // Create DFA from NFA
    explicit DFALexer(const NFALexer& nfa);

    // Optimize DFA
    void optimize();
    // Returns longest match in the form of (length, token)
    optional<pair<size_t, TokenID>> run(const string& s) const override;

    size_t size() { return table.size(); }

    // Convert lexer DFA to TextMate grammar JSON (based on regular expressions)
    // Following: https://macromates.com/manual/en/regular_expressions (only a simple subset is used)
    // (Not implemented)
    string toTextMateGrammar() const;

  private:
    // The transition & accepting state table
    struct Entry {
      bool has[0x100];
      State tr[0x100];
      optional<TokenID> ac;
      Entry(): has{}, tr{}, ac(nullopt) {}
    };
    vector<Entry> table;

    // The initial state
    State initial;

    friend class PowersetConstruction;
    friend class PartitionRefinement;
  };

}

#endif // LEXER_HPP_
