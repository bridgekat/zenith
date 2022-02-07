#include <iostream>
#include <utility>
#include <string>
#include <optional>
#include <sstream>
#include <fstream>
#include "parsing/parser.hpp"

using std::string;
using std::optional, std::make_optional, std::nullopt;
using std::cin, std::cout, std::endl;
using Parsing::Token, Parsing::TokenID;
using Parsing::NFALexer, Parsing::DFALexer;


class TestLexer: public NFALexer {
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
  TestLexer nfa;
  DFALexer test(nfa);

  cout << nfa.table.size() << endl;
  cout << test.table.size() << endl;
  test.optimize();
  cout << test.table.size() << endl;

  std::ifstream in("test.txt");
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

  while (!test.eof()) {
    auto next = test.getNextToken();
    if (!next) {
      cout << "Parse error at: "
           << test.rest.substr(0, cutoff(test.rest, 20))
           << "...: no prefix matches known patterns "
              "(most probably due to unsupported ASCII character combinations. "
              "Is file encoded in UTF-8 and your syntax correct?)" << endl;
      test.ignoreNextCodepoint();
    } else cout << TestLexer::printToken(next.value()) << endl;
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
