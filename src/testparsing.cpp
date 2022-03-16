#include <utility>
#include <string>
#include <vector>
#include <optional>
#include <iostream>
#include <fstream>
#include <sstream>
#include "core.hpp"
#include "parsing/languages/apimu.hpp"

using std::pair, std::string, std::vector;
using std::optional, std::make_optional, std::nullopt;
using std::cin, std::cout, std::endl;
using Parsing::Token, Parsing::Symbol;
using Parsing::NFALexer, Parsing::DFALexer;
using Parsing::ParseTree, Parsing::EarleyParser;

// See: https://stackoverflow.com/questions/116038/how-do-i-read-an-entire-file-into-a-stdstring-in-c
string readFile(std::ifstream& in) {
  std::ostringstream sstr;
  sstr << in.rdbuf();
  return sstr.str();
}

int main() {
  std::ifstream in("notes/test.mu");
  string content = readFile(in);
  in.close();

  Parsing::ApiMuLanguage apimu;
  apimu.parse<Parsing::ApiMuLanguage::Decls>(content);

  /*
  enum Terminal: TokenID { B };
  enum Nonterminal: TokenID { S };
  vector<Token> str = { { B, "" }, { B, "" }, { B, "" } };

  EarleyParser parser;
  parser.rules.push_back({ S, { { true, B } } });
  parser.rules.push_back({ S, { { false, S }, { false, S } } });

  parser.start = S;
  vector<vector<EarleyParser::State>> dpa = parser.rustr);
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
