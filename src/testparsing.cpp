#include <utility>
#include <string>
#include <vector>
#include <optional>
#include <iostream>
#include <fstream>
#include <sstream>
#include "core.hpp"
#include "parsing/language.hpp"

using std::pair, std::string, std::vector;
using std::optional, std::make_optional, std::nullopt;
using std::cin, std::cout, std::endl;
using Parsing::Token, Parsing::Symbol;
using Parsing::NFALexer, Parsing::DFALexer;
using Parsing::ParseTree, Parsing::EarleyParser;


enum ESymbolID: Symbol {
  BLANK = 0, LINE_COMMENT, BLOCK_COMMENT, DIRECTIVE,
  NATURAL, STRING,
  OP_COMMA, OP_SEMICOLON, OP_LBRACE, OP_RBRACE, OP_RRARROW, OP_SLASH,
  KW_ANY, KW_ANYFUNC, KW_ANYPRED, KW_ASSUME, KW_NAME, KW_PROOF,
  OPERATOR, IDENTIFIER,

  DECLS, DECL, BLOCK,
  ASSERTION, OPT_NAME, OPT_PROOF,
  ASSUME, ASSUMPTIONS, ASSUMPTION,
  ANY, VARS, VAR,
  ANYFUNC, FUNCS, FUNC,
  ANYPRED, PREDS, PRED,
  EXPR, IDENTS, IDENT
};

const vector<string> names = {
  "blank", "line-comment", "block-comment", "directive",
  "natural", "string",
  ",", ";", "{", "}", "=>", "/",
  "any", "anyfunc", "anypred", "assume", "name", "proof",
  "operator", "identifier",

  "decl-list", "decl", "block",
  "assertion", "opt-name", "opt-proof",
  "assume", "assumption-list", "assumption",
  "any", "var-list", "var",
  "anyfunc", "func-list", "func",
  "anypred", "pred-list", "pred",
  "expr", "ident-list", "ident",
};


class TestLexer: public NFALexer {
public:

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
    vector<pair<Symbol, string>> op = {
      { OP_COMMA,     ","  },
      { OP_SEMICOLON, ";"  },
      { OP_LBRACE,    "{"  },
      { OP_RBRACE,    "}"  },
      { OP_RRARROW,   "=>" },
      { OP_SLASH,     "/"  },
    };
    for (const auto& [id, lexeme]: op) addPattern(id, word(lexeme));
    vector<pair<Symbol, string>> kw = {
      { KW_ANY,     "any"     },
      { KW_ANYFUNC, "anyfunc" },
      { KW_ANYPRED, "anypred" },
      { KW_ASSUME,  "assume"  },
      { KW_NAME,    "name"    },
      { KW_PROOF,   "proof"   },
    };
    for (const auto& [id, lexeme]: kw) addPattern(id, word(lexeme));
    addPattern(OPERATOR,
      alt({ ch({ '=', '+', '-', '*', '\\', '%', '&', '(', ')', ':', '?', '[', ']', '^', '|', '<', '>' }),
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

  cout << nfa.size() << endl;
  cout << test.size() << endl;
  test.optimize();
  cout << test.size() << endl;
  cout << endl;

  std::ifstream in("notes/test.mu");
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
           << test.getRest().substr(0, cutoff(test.getRest(), 20))
           << "...: no prefix matches known patterns "
              "(most probably due to unsupported ASCII character combinations. "
              "Is file encoded in UTF-8 and your syntax correct?)" << endl;
      test.ignoreNextCodepoint();
    } else {
      Token tok = next.value();
      using enum ESymbolID;
      switch (tok.id) {
        case BLANK: case LINE_COMMENT: case BLOCK_COMMENT: break;
        default:
          str.push_back(tok);
          break;
      }
    }
  }
  cout << "Scanning complete" << endl;

  EarleyParser parser;
  parser.start = DECLS;

  #define rule(sym_, ...) parser.rules.push_back({ sym_, { __VA_ARGS__ } });

  rule(DECLS);
  rule(DECLS, DECLS, DECL);

  rule(DECL, BLOCK);
  rule(DECL, DIRECTIVE);
  rule(DECL, ASSERTION);
  rule(DECL, ASSUME);
  rule(DECL, ANY);
  rule(DECL, ANYFUNC);
  rule(DECL, ANYPRED);

  rule(BLOCK, OP_LBRACE, DECLS, OP_RBRACE);

  rule(ASSERTION, OP_RRARROW, EXPR, OPT_NAME, OPT_PROOF, OP_SEMICOLON);
  rule(OPT_NAME);
  rule(OPT_NAME, KW_NAME, IDENTIFIER);
  rule(OPT_PROOF);
  rule(OPT_PROOF, KW_PROOF, EXPR);

  rule(ASSUME, KW_ASSUME, ASSUMPTIONS, DECL);
  rule(ASSUMPTIONS, ASSUMPTION);
  rule(ASSUMPTIONS, ASSUMPTIONS, OP_COMMA, ASSUMPTION);
  rule(ASSUMPTIONS, ASSUMPTIONS, OP_COMMA); // Optional commas anywhere!
  rule(ASSUMPTION, EXPR, OPT_NAME);

  rule(ANY, KW_ANY, VARS, DECL);
  rule(VARS, VAR);
  rule(VARS, VARS, OP_COMMA, VAR);
  rule(VARS, VARS, OP_COMMA); // Optional commas anywhere!
  rule(VAR, IDENTIFIER);

  rule(ANYFUNC, KW_ANYFUNC, FUNCS, DECL);
  rule(FUNCS, FUNC);
  rule(FUNCS, FUNCS, OP_COMMA, FUNC);
  rule(FUNCS, FUNCS, OP_COMMA);
  rule(FUNC, IDENTIFIER, OP_SLASH, NATURAL);

  rule(ANYPRED, KW_ANYPRED, PREDS, DECL);
  rule(PREDS, PRED);
  rule(PREDS, PREDS, OP_COMMA, PRED);
  rule(PREDS, PREDS, OP_COMMA);
  rule(PRED, IDENTIFIER, OP_SLASH, NATURAL);

  rule(EXPR, IDENTS);
  rule(IDENTS, IDENT);
  rule(IDENTS, IDENTS, IDENT);
  rule(IDENT, OPERATOR);
  rule(IDENT, IDENTIFIER);

  #undef rule

  ///*
  typedef EarleyParser::LinkedState LinkedState;

  parser.str = str;
  parser.run();
  vector<vector<LinkedState>> dpa = parser.dpa;
  if (dpa.size() != str.size() + 1) throw Core::Unreachable();

  for (size_t pos = 0; pos <= str.size(); pos++) {
    cout << "States at position " << pos << ":" << endl;
    for (const LinkedState& ls: dpa[pos]) {
      cout << parser.showState(ls.state, names) << endl;
    }
    cout << endl;
    if (pos < str.size()) cout << "Next token: <" << names[str[pos].id] << ">" << endl;
  }
  //*/

  /*
  Core::Allocator<ParseTree> pool;
  ParseTree* tree = parser.parse(str, pool);
  */

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
