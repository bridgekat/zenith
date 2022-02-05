#include <iostream>
#include <sstream>
#include <fstream>
#include "lexer.h"

namespace Lexer {
  typedef NFALexer::State State;
  typedef NFALexer::NFA NFA;
  typedef NFALexer::TokenID TokenID;
  typedef NFALexer::Token Token;

  optional<pair<size_t, TokenID>> NFALexer::run(const string& str) const {
    optional<pair<size_t, TokenID>> res = nullopt;
    vector<State> s;
    vector<bool> v(table.size(), false);

    // A helper function
    auto closure = [&v, this] (vector<State>& s) {
      // Expand to epsilon closure (using DFS)
      vector<State> stk = s;
      while (!stk.empty()) {
        State x = stk.back(); stk.pop_back();
        for (auto [cc, u]: table[x].tr) if (cc == 0 && !v[u]) {
          s.push_back(u);
          stk.push_back(u);
          v[u] = true;
        }
      }
      // Reset v[] to false
      for (State x: s) v[x] = false;
    };

    s.push_back(initial);
    v[initial] = true;
    closure(s);
    for (size_t i = 0; i < str.size(); i++) {
      unsigned char c = str[i];
      // Move one step
      vector<State> t;
      for (State x: s) for (auto [cc, u]: table[x].tr) if (cc == c) {
        t.push_back(u);
        v[u] = true;
      }
      closure(t);
      s.swap(t);
      // Update result if reaches accepting state
      // Patterns with smaller IDs have higher priority
      optional<TokenID> curr = nullopt;
      for (State x: s) if (table[x].ac) {
        if (!curr || curr.value() > table[x].ac.value()) curr = table[x].ac;
      }
      // Update longest match, if applicable
      if (curr) res = { i + 1, curr.value() };
      // Exit if no more possible matches
      if (s.empty()) break;
    }
    return res;
  }

  optional<Token> NFALexer::getNextToken() {
    auto opt = run(rest);
    if (!opt) return nullopt;
    auto [len, id] = opt.value();
    Token res{ id, rest.substr(0, len) };
    rest = rest.substr(len);
    return res;
  }
}


using std::string;
using std::optional, std::make_optional, std::nullopt;
using std::cin, std::cout, std::endl;

class TestLexer: public Lexer::NFALexer {
public:
  enum ETokenID: TokenID {
    BLANK = 0, LINE_COMMENT, BLOCK_COMMENT, PREPROCESSOR,
    NATURAL, STRING, DELIMITER, OPERATOR, KEYWORD, IDENTIFIER
  };

  TestLexer(): NFALexer() {
    addPattern(ETokenID::BLANK,
      star(ch({ ' ', '\t', '\n', '\v', '\f', '\r' })));
    addPattern(ETokenID::LINE_COMMENT,
      concat(word("//"), star(except({ '\r', '\n' }))));
    addPattern(ETokenID::BLOCK_COMMENT,
      concat(word("/*"),
        star(concat(star(except({ '*' })), plus(ch({ '*' })), except({ '/' }))),
                    star(except({ '*' })), plus(ch({ '*' })), ch({ '/' })));
    addPattern(ETokenID::PREPROCESSOR,
      concat(ch({ '#' }), star(except({ '\r', '\n' }))));
    addPattern(ETokenID::NATURAL,
      alt({ star(range('0', '9')),
            concat(ch({ '0' }), ch({ 'x', 'X' }), star(alt({ range('0', '9'), range('a', 'f'), range('A', 'F') }))) }));
    addPattern(ETokenID::STRING,
      concat(ch({ '"' }), star(alt({ except({ '"', '\\' }), concat(ch({ '\\' }), ch({ '"', '\\' })) })), ch({ '"' })));
    addPattern(ETokenID::DELIMITER,
      ch({ '{', '}', ';' }));
    addPattern(ETokenID::OPERATOR,
      alt({ ch({ '+', '-', '*', '/', '\\', '%', '&', '(', ')', ',', ':', '?', '[', ']', '^', '|', '<', '>', '=', '`' }),
            word("->"), word("<->"), word("↑"), word("=>"), word(":="), word("::"), word(":<->") }));
    addPattern(ETokenID::KEYWORD,
      alt({ word("any"), word("anyfunc"), word("anypred"), word("assume"), word("def"), word("idef"), word("undef"),
            word("proof"), word("by"), word("name"), word("namespace"), word("private"), word("public"),
            word("and"), word("or"), word("implies"), word("not"), word("iff"), word("true"), word("false"), word("eq"),
            word("forall"), word("exists"), word("unique"), word("forallfunc"), word("forallpred") }));
    addPattern(ETokenID::IDENTIFIER,
      concat(
        alt({ range('a', 'z'), range('A', 'Z'), ch({ '_' }), utf8segment() }),
        star(alt({ range('a', 'z'), range('A', 'Z'), range('0', '9'), ch({ '_', '\'', '.' }), utf8segment() }))));
  }

  optional<Token> getNextToken() override {
    auto res = NFALexer::getNextToken();
    while (res && res.value().first == BLANK) res = NFALexer::getNextToken();
    return res;
  }

  static string printToken(const Token& tok) {
    switch (tok.first) {
      case BLANK:         return "Blank of length " + std::to_string(tok.second.size());
      case LINE_COMMENT:  return "Line comment [" + tok.second + "]";
      case BLOCK_COMMENT: return "Block comment [" + tok.second + "]";
      case PREPROCESSOR:  return "Preprocessor [" + tok.second + "]";
      case NATURAL:       return "Natural [" + tok.second + "]";
      case STRING:        return "String [" + tok.second + "]";
      case DELIMITER:     return "Delimiter [" + tok.second + "]";
      case OPERATOR:      return "Operator [" + tok.second + "]";
      case KEYWORD:       return "Keyword [" + tok.second + "]";
      case IDENTIFIER:    return "Identifier [" + tok.second + "]";
      default:            return "Unknown [" + tok.second + "]";
    }
  }
};

// See: https://stackoverflow.com/questions/116038/how-do-i-read-an-entire-file-into-a-stdstring-in-c
string readFile(std::ifstream& in) {
  std::ostringstream sstr;
  sstr << in.rdbuf();
  return sstr.str();
}

int main() {
  TestLexer test;

  std::ifstream in("test.txt");
  test << readFile(in);
  in.close();

  while (true) {
    auto next = test.getNextToken();
    if (!next) break;
    cout << TestLexer::printToken(next.value()) << endl;
  }

  /*
  // See: https://en.cppreference.com/w/cpp/locale/wstring_convert/converted
  // The UTF-8 - UTF-32 standard conversion facet
  std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> cvt;

  // UTF-8 to UTF-32
  std::u32string utf32 = cvt.from_bytes(s);
  cout << "New UTF-32 string size: " << utf32.size() << '\n';
  cout << "converted() == " << cvt.converted() << '\n';

  // UTF-32 to UTF-8
  std::string utf8 = cvt.to_bytes(utf32);
  cout << "New UTF-8 string size: " << utf8.size() << '\n';
  cout << "converted() == " << cvt.converted() << '\n';

  cout << utf8 << endl;
  */

  return 0;
}
