#include <initializer_list>
#include <vector>
#include <algorithm>
#include <optional>
#include <string>


namespace Lexer {
  using std::initializer_list;
  using std::vector;
  using std::pair, std::make_pair;
  using std::optional, std::make_optional, std::nullopt;
  using std::string;

  typedef unsigned int TokenID;
  typedef pair<TokenID, string> Token;

  class NFALexer {
  public:
    typedef unsigned int State;
    typedef pair<State, State> NFA;

    // The transition & accepting state table
    struct Entry {
      vector<pair<unsigned char, State>> tr;
      optional<TokenID> ac;
      Entry(): tr(), ac() {}
    };
    vector<Entry> table;

    // The initial state
    State initial;
    string rest;

    // Create initial state
    NFALexer(): table(), initial(0), rest() { table.emplace_back(); }
    virtual ~NFALexer() = default;

    #define node(x) State x = table.size(); table.emplace_back()
    #define trans(s, c, t) table[s].tr.emplace_back(c, t)

    // Add pattern (mark accepting state)
    void addPattern(TokenID id, NFA nfa) {
      trans(initial, 0, nfa.first);
      auto& o = table[nfa.second].ac;
      if (!o.has_value()) o = id;
    }

    // Returns longest match in the form of (length, token)
    optional<pair<size_t, TokenID>> run(const string& s) const;

    // getNextToken from rest
    bool eof() { return rest.empty(); }
    NFALexer& operator<< (const string& s) { rest += s; return *this; }
    virtual optional<Token> getNextToken();
    void ignoreNextCodepoint();

    // Some useful NFA constructors
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

    NFA any()         { return range(0x01, 0xFF); }
    NFA utf8segment() { return range(0x80, 0xFF); }
    NFA except(const initializer_list<unsigned char>& ls) {
      vector<bool> f(0x100, true);
      for (auto c: ls) f[c] = false;
      node(s); node(t);
      for (unsigned int i = 0x01; i <= 0xFF; i++) if (f[i]) trans(s, i, t);
      return { s, t };
    }
    NFA plus(NFA a) { return concat2(a, star(a)); }

    #undef node
    #undef trans
  };

  class DFALexer {
  public:
    typedef unsigned int State;

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
    string rest;

    // Create initial state
    DFALexer(): table(), initial(0), rest() { table.emplace_back(); }
    // Create DFA from NFA
    DFALexer(const NFALexer& nfa);
    virtual ~DFALexer() = default;

    // Optimize DFA
    void optimize();
    // Returns longest match in the form of (length, token)
    optional<pair<size_t, TokenID>> run(const string& s) const;

    // getNextToken from rest
    bool eof() { return rest.empty(); }
    DFALexer& operator<< (const string& s) { rest += s; return *this; }
    virtual optional<Token> getNextToken();
    void ignoreNextCodepoint();
  };
}
