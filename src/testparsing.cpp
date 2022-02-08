#include <utility>
#include <string>
#include <vector>
#include <optional>
#include <iostream>
#include <fstream>
#include <sstream>
#include "parsing/parser.hpp"

using std::pair, std::string, std::vector;
using std::optional, std::make_optional, std::nullopt;
using std::cin, std::cout, std::endl;
using Parsing::Token, Parsing::TokenID;
using Parsing::NFALexer, Parsing::DFALexer;
using Parsing::EarleyParser;


class TestLexer: public NFALexer {
public:
  enum ETokenID: TokenID {
    BLANK = 0, LINE_COMMENT, BLOCK_COMMENT, DIRECTIVE,
    NATURAL, STRING,
    KW_ANY, KW_ANYFUNC, KW_ANYPRED, KW_ASSUME, KW_NAME, KW_PROOF,
    OP_COMMA, OP_SEMICOLON, OP_LBRACE, OP_RBRACE, OP_RRARROW,
    IDENTIFIER
  };

  TestLexer(): NFALexer() {
    addPattern(BLANK,
      star(ch({ ' ', '\t', '\n', '\v', '\f', '\r' })));
    addPattern(LINE_COMMENT,
      concat(word("//"), star(except({ '\r', '\n' }))));
    addPattern(BLOCK_COMMENT,
      concat(word("/*"),
        star(concat(star(except({ '*' })), plus(ch({ '*' })), except({ '/' }))),
                    star(except({ '*' })), plus(ch({ '*' })), ch({ '/' })));
    addPattern(DIRECTIVE,
      concat(ch({ '#' }), star(except({ '\r', '\n' }))));
    addPattern(NATURAL,
      alt({ star(range('0', '9')),
            concat(ch({ '0' }), ch({ 'x', 'X' }), star(alt({ range('0', '9'), range('a', 'f'), range('A', 'F') }))) }));
    addPattern(STRING,
      concat(ch({ '"' }), star(alt({ except({ '"', '\\' }), concat(ch({ '\\' }), ch({ '"', '\\' })) })), ch({ '"' })));
    /*
    addPattern(OPERATOR,
      alt({ ch({ '+', '-', '*', '/', '\\', '%', '&', '(', ')', ',', ':', '?', '[', ']', '^', '|', '<', '>', '=', '`' }),
            word("->"), word("<->"), word("↑"), word("=>"), word(":="), word("::"), word(":<->") }));
    addPattern(KEYWORD,
      alt({ word("any"), word("anyfunc"), word("anypred"), word("assume"), word("def"), word("idef"), word("undef"),
            word("proof"), word("by"), word("name"), word("namespace"), word("private"), word("public"),
            word("and"), word("or"), word("implies"), word("not"), word("iff"), word("true"), word("false"), word("eq"),
            word("forall"), word("exists"), word("unique"), word("forallfunc"), word("forallpred") }));
    */

    vector<pair<TokenID, string>> kw = {
      { KW_ANY,     "any"     },
      { KW_ANYFUNC, "anyfunc" },
      { KW_ANYPRED, "anypred" },
      { KW_ASSUME,  "assume"  },
      { KW_NAME,    "name"    },
      { KW_PROOF,   "proof"   },
    };
    for (const auto& [id, lexeme]: kw) addPattern(id, word(lexeme));

    vector<pair<TokenID, string>> op = {
      { OP_COMMA,     ","  },
      { OP_SEMICOLON, ";"  },
      { OP_LBRACE,    "{"  },
      { OP_RBRACE,    "}"  },
      { OP_RRARROW,   "=>" },
    };
    for (const auto& [id, lexeme]: op) addPattern(id, word(lexeme));

    addPattern(IDENTIFIER,
      concat(
        alt({ range('a', 'z'), range('A', 'Z'), ch({ '_' }), utf8segment() }),
        star(alt({ range('a', 'z'), range('A', 'Z'), range('0', '9'), ch({ '_', '\'', '.' }), utf8segment() }))));
  }
};


// See: https://stackoverflow.com/questions/116038/how-do-i-read-an-entire-file-into-a-stdstring-in-c
string readFile(std::ifstream& in) {
  std::ostringstream sstr;
  sstr << in.rdbuf();
  return sstr.str();
}

int main() {
  TestLexer nfa;
  DFALexer test(nfa);

  cout << nfa.table.size() << endl;
  cout << test.table.size() << endl;
  test.optimize();
  cout << test.table.size() << endl;

  std::ifstream in("test1.txt");
  test << readFile(in);
  in.close();

  // Avoid cutting UTF-8 segments
  auto cutoff = [] (const string& s, size_t pos) {
    for (; pos < s.size(); pos++) {
      unsigned char c = s[pos];
      if ((c & 0b11000000) != 0b10000000) break;
    }
    return pos;
  };

  vector<Token> str;
  while (!test.eof()) {
    auto next = test.getNextToken();
    if (!next) {
      cout << "Parse error at: "
           << test.rest.substr(0, cutoff(test.rest, 20))
           << "...: no prefix matches known patterns "
              "(most probably due to unsupported ASCII character combinations. "
              "Is file encoded in UTF-8 and your syntax correct?)" << endl;
      test.ignoreNextCodepoint();
    } else {
      Token tok = next.value();
      using enum TestLexer::ETokenID;
      switch (tok.id) {
        case BLANK: case LINE_COMMENT: case BLOCK_COMMENT: case DIRECTIVE: break;
        default:
          str.push_back(tok);
          break;
      }
    }
  }

  /*
  enum Terminal: TokenID { B };
  enum Nonterminal: TokenID { S };
  vector<Token> str = { { B, "" }, { B, "" }, { B, "" } };

  EarleyParser parser;
  parser.rules.push_back({ S, { { true, B } } });
  parser.rules.push_back({ S, { { false, S }, { false, S } } });

  parser.start = S;
  vector<vector<EarleyParser::State>> states = parser.run(str);
  */

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
