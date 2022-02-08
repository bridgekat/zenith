#include <utility>
#include <string>
#include <vector>
#include <optional>
#include <iostream>
#include <fstream>
#include <sstream>
#include "core/base.hpp"
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
    OP_COMMA, OP_SEMICOLON, OP_LBRACE, OP_RBRACE, OP_RRARROW,
    KW_ANY, KW_ANYFUNC, KW_ANYPRED, KW_ASSUME, KW_NAME, KW_PROOF,
    OPERATOR, IDENTIFIER,
  };
  inline static const vector<string> tNames = {
    "blank", "line-comment", "block-comment", "directive",
    "natural", "string",
    ",", ";", "{", "}", "=>",
    "any", "anyfunc", "anypred", "assume", "name", "proof",
    "operator", "identifier",
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
    addPattern(KEYWORD,
      alt({ word("any"), word("anyfunc"), word("anypred"), word("assume"), word("def"), word("idef"), word("undef"),
            word("proof"), word("by"), word("name"), word("namespace"), word("private"), word("public"),
            word("and"), word("or"), word("implies"), word("not"), word("iff"), word("true"), word("false"), word("eq"),
            word("forall"), word("exists"), word("unique"), word("forallfunc"), word("forallpred") }));
    */

    vector<pair<TokenID, string>> op = {
      { OP_COMMA,     ","  },
      { OP_SEMICOLON, ";"  },
      { OP_LBRACE,    "{"  },
      { OP_RBRACE,    "}"  },
      { OP_RRARROW,   "=>" },
    };
    for (const auto& [id, lexeme]: op) addPattern(id, word(lexeme));

    vector<pair<TokenID, string>> kw = {
      { KW_ANY,     "any"     },
      { KW_ANYFUNC, "anyfunc" },
      { KW_ANYPRED, "anypred" },
      { KW_ASSUME,  "assume"  },
      { KW_NAME,    "name"    },
      { KW_PROOF,   "proof"   },
    };
    for (const auto& [id, lexeme]: kw) addPattern(id, word(lexeme));

    addPattern(OPERATOR,
      alt({ ch({ '=', '+', '-', '*', '/', '\\', '%', '&', '(', ')', ':', '?', '[', ']', '^', '|', '<', '>' }),
            word("->"), word("<->"), word("↑") }));
    addPattern(IDENTIFIER,
      concat(
        alt({ range('a', 'z'), range('A', 'Z'), ch({ '_', '`' }), utf8segment() }),
        star(alt({ range('a', 'z'), range('A', 'Z'), range('0', '9'), ch({ '_', '`', '\'', '.' }), utf8segment() }))));
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
  cout << endl;

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
        case BLANK: case LINE_COMMENT: case BLOCK_COMMENT: break;
        default:
          str.push_back(tok);
          break;
      }
    }
  }
  cout << "Scanning complete" << endl;

  enum Nonterminal: TokenID {
    DECLS, DECL, BLOCK,
    ASSERTION, OPT_NAME, OPT_PROOF,
    ASSUME, ASSUMPTIONS, ASSUMPTION,
    ANY, VARS, VAR,
    EXPR, IDENTS, IDENT, // TEMP CODE
  };
  vector<string> nNames = {
    "decl-list", "decl", "block",
    "assertion", "opt-name", "opt-proof",
    "assume", "assumption-list", "assumption",
    "any", "vars", "var",
    "expr", "ident-list", "ident", // TEMP CODE
  };

  EarleyParser parser;
  parser.start = DECLS;

  #define term(id_) { true, TestLexer::ETokenID::id_ }
  #define n(id_) { false, Nonterminal::id_ }
  #define rule(sym_, ...) parser.rules.push_back({ sym_, { __VA_ARGS__ } });

  rule(DECLS, n(DECL)); // TODO: support empty rule
  rule(DECLS, n(DECLS), n(DECL));

  rule(DECL, n(BLOCK));
  rule(DECL, term(DIRECTIVE));
  rule(DECL, n(ASSERTION));
  rule(DECL, n(ASSUME));
  rule(DECL, n(ANY));

  rule(BLOCK, term(OP_LBRACE), n(DECLS), term(OP_RBRACE));

  rule(ASSERTION, term(OP_RRARROW), n(EXPR), n(OPT_NAME), n(OPT_PROOF), term(OP_SEMICOLON));
  rule(OPT_NAME);
  rule(OPT_NAME, term(KW_NAME), term(IDENTIFIER));
  rule(OPT_PROOF);
  rule(OPT_PROOF, term(KW_PROOF), n(EXPR));

  rule(ASSUME, term(KW_ASSUME), n(ASSUMPTIONS), n(DECL));
  rule(ASSUMPTIONS, n(ASSUMPTION));
  rule(ASSUMPTIONS, n(ASSUMPTIONS), term(OP_COMMA), n(ASSUMPTION));
  rule(ASSUMPTIONS, n(ASSUMPTIONS), term(OP_COMMA)); // Optional commas anywhere!
  rule(ASSUMPTION, n(EXPR), n(OPT_NAME));

  rule(ANY, term(KW_ANY), n(VARS), n(DECL));
  rule(VARS, n(VAR));
  rule(VARS, n(VARS), term(OP_COMMA), n(VAR));
  rule(VARS, n(VARS), term(OP_COMMA)); // Optional commas anywhere!
  rule(VAR, term(IDENTIFIER));

  rule(EXPR, n(IDENTS));
  rule(IDENTS, n(IDENT));
  rule(IDENTS, n(IDENTS), n(IDENT));
  rule(IDENT, term(OPERATOR));
  rule(IDENT, term(IDENTIFIER));

  #undef term
  #undef n
  #undef rule

  typedef EarleyParser::State State;
  const auto& tNames = TestLexer::tNames;

  vector<vector<State>> states = parser.run(str);
  if (states.size() != str.size() + 1) throw Core::Unreachable();

  for (size_t pos = 0; pos <= str.size(); pos++) {
    cout << "States at position " << pos << ":" << endl;
    for (const State& s: states[pos]) {
      cout << parser.showState(s, tNames, nNames) << endl;
    }
    cout << endl;
    if (pos < str.size()) cout << "Next token: <" << tNames[str[pos].id] << ">" << endl;
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
