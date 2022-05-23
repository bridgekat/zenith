#include <iostream>
#include <string>
#include <vector>
#include <fstream>
#include <sstream>
#include "core.hpp"
#include "eval/sexpr.hpp"
#include "eval/environment.hpp"

using std::string;
using std::vector;
using std::cin, std::cout, std::endl;
using Core::Allocator;
using Parsing::ParseTree, Parsing::makePrec;


class Lisp: public Parsing::Language {
public:

  // ===================
  // Symbol declarations
  // ===================

  // Terminal symbols

  struct Blank {};
  struct LParen {};
  struct RParen {};
  struct LBracket {};
  struct RBracket {};
  struct Point {};
  struct Quote {};
  struct Comma {};
  struct Atsign {};

  using Symbol = Eval::Symbol;
  using Number = Eval::Number;
  using String = Eval::String;
  using Boolean = Eval::Boolean;
  using Undefined = Eval::Undefined;

  // Nonterminal symbols

  struct List { Eval::SExpr* e; };
  struct ListInner { Eval::SExpr* e; };
  struct SExprStar { vector<Eval::SExpr*> es; }; // Zero or more `SExpr`s
  struct SExprPlus { vector<Eval::SExpr*> es; }; // One or more `SExpr`s
  struct SExpr { Eval::SExpr* e; };
  struct Statement { Eval::SExpr* e; }; // Start symbol

  Lisp(): pool(), env() {

    // ====================================
    // Patterns, rules and semantic actions
    // ====================================

    // Terminal symbols
    // See: https://github.com/digama0/mm0/blob/master/mm0-hs/mm1.md#s-expressions

    #define epsilon     lexer.epsilon
    #define ch          lexer.ch
    #define range       lexer.range
    #define concat      lexer.concat
    #define word        lexer.word
    #define alt         lexer.alt
    #define star        lexer.star
    #define opt         lexer.opt
    #define plus        lexer.plus
    #define any         lexer.any
    #define utf8segment lexer.utf8segment
    #define except      lexer.except

    addPattern([] (const string&) -> Blank { return {}; },
      star(ch(' ', '\t', '\n', '\v', '\f', '\r')));
    addPattern([] (const string&) -> Blank { return {}; },
      concat(word("//"), star(except('\r', '\n'))));
    addPattern([] (const string&) -> Blank { return {}; },
      concat(word("/*"),
        star(concat(star(except('*')), plus(ch('*')), except('/'))),
                    star(except('*')), plus(ch('*')), ch('/')));
    setAsIgnoredSymbol<Blank>();

    addPattern([] (const string&) -> LParen { return {}; }, word("("));
    addPattern([] (const string&) -> RParen { return {}; }, word(")"));
    addPattern([] (const string&) -> LBracket { return {}; }, word("["));
    addPattern([] (const string&) -> RBracket { return {}; }, word("]"));
    addPattern([] (const string&) -> Point { return {}; }, word("."));
    addPattern([] (const string&) -> Quote { return {}; }, word("'"));
    addPattern([] (const string&) -> Comma { return {}; }, word(","));
    addPattern([] (const string&) -> Atsign { return {}; }, word("@"));

    addPattern([] (const string& lexeme) -> Symbol { return { lexeme }; },
      alt(
        concat(alt(range('a', 'z'), range('A', 'Z'),                  ch('!', '%', '&', '*', '/', ':', '<', '=', '>', '?', '^', '_', '~'), utf8segment()),
          star(alt(range('a', 'z'), range('A', 'Z'), range('0', '9'), ch('!', '%', '&', '*', '/', ':', '<', '=', '>', '?', '^', '_', '~', '+', '-', '.', '@'), utf8segment()))),
        word("+"),
        word("-"),
        word("...")
      ));
    addPattern([] (const string& lexeme) -> Number { return std::stoi(lexeme); },
      alt(plus(range('0', '9')),
          concat(ch('0'), ch('x', 'X'), plus(alt(range('0', '9'), range('a', 'f'), range('A', 'F'))))));
    addPattern([] (const string& lexeme) -> String { return Eval::SExpr::unescapeString(lexeme.substr(1, lexeme.size() - 2)); },
      concat(ch('"'), star(alt(except('"', '\\'), concat(ch('\\'), ch('"', '\\', 'a', 'b', 'f', 'n', 'r', 't', 'v')))), ch('"')));
    addPattern([] (const string&) -> Boolean { return Boolean::True; },  alt(word("#true"), word("#t")));
    addPattern([] (const string&) -> Boolean { return Boolean::False; }, alt(word("#false"), word("#f")));
    addPattern([] (const string&) -> Undefined { return {}; },  alt(word("#undefined"), word("#u")));

    #undef epsilon
    #undef ch
    #undef range
    #undef concat
    #undef word
    #undef alt
    #undef star
    #undef opt
    #undef plus
    #undef any
    #undef utf8segment
    #undef except
    #undef trivial

    // Nonterminal symbols
    // See: https://github.com/digama0/mm0/blob/master/mm0-hs/mm1.md#s-expressions

    addRule([]     (LParen, ListInner&& inner, RParen)        -> List { return { inner.e }; });
    addRule([]     (LBracket, ListInner&& inner, RBracket)    -> List { return { inner.e }; });
    addRule([this] (SExprStar&& star)                         -> ListInner { return { makeList(std::move(star.es)) }; });
    addRule([this] (SExprPlus&& plus, Point, SExpr&& e)       -> ListInner { return { makeList(std::move(plus.es), e.e) }; });
    addRule([this] (SExprStar&& star, Atsign, ListInner&& r)  -> ListInner { star.es.push_back(r.e); return { makeList(std::move(star.es)) }; });
    addRule([]     ()                                         -> SExprStar { return { {} }; });
    addRule([]     (SExprStar&& star, SExpr&& e)              -> SExprStar { star.es.push_back(e.e); return { star.es }; });
    addRule([]     (SExpr&& e)                                -> SExprPlus { return { { e.e } }; });
    addRule([]     (SExprPlus&& plus, SExpr&& e)              -> SExprPlus { plus.es.push_back(e.e); return { plus.es }; });

    addRule([]     (List&& list)        -> SExpr { return { list.e }; });
    addRule([this] (Symbol&& sym)       -> SExpr { return { pool.emplaceBack(std::move(sym)) }; });
    addRule([this] (Number&& num)       -> SExpr { return { pool.emplaceBack(std::move(num)) }; });
    addRule([this] (String&& str)       -> SExpr { return { pool.emplaceBack(std::move(str)) }; });
    addRule([this] (Boolean&& boolean)  -> SExpr { return { pool.emplaceBack(std::move(boolean)) }; });
    addRule([this] (Undefined&& undef)  -> SExpr { return { pool.emplaceBack(std::move(undef)) }; });
    addRule([this] (Quote, SExpr&& e)   -> SExpr { return { makeList({ pool.emplaceBack(Symbol{ "quote" }), e.e }) }; });
    addRule([this] (Comma, SExpr&& e)   -> SExpr { return { makeList({ pool.emplaceBack(Symbol{ "unquote" }), e.e }) }; });
    addRule([]     (SExpr&& e)          -> Statement { return { e.e }; });

  }

  Eval::SExpr* makeList(vector<Eval::SExpr*>&& a, Eval::SExpr* tail = nullptr) {
    Eval::SExpr* res = tail? tail : pool.emplaceBack(Eval::Nil{});
    for (auto it = a.rbegin(); it != a.rend(); it++) res = pool.emplaceBack(*it, res); // NOLINT(modernize-loop-convert)
    return res;
  }

  // ====================
  // Read-eval-print loop
  // ====================

  void evalPrint(const string& str) {
    lexer.setString(str);
    while (!parser.eof()) {
      const auto& opt = Language::nextSentence<Statement>();
      const auto& err = Language::popParsingErrors();
      if (!err.empty()) {
        const auto& ex = err[0];
        cout << endl;
        cout << "× " << ex.what() << endl;
        cout << "| " << endl;
        cout << "| " << str << endl;
        cout << "| " << std::string(ex.startPos, ' ')
                     << std::string(ex.endPos - ex.startPos, '~') << endl;
        cout << endl;
        return;
      }
      if (!opt) break;
      const auto& e = opt->e;
      try {
        const auto& res = env.evalStatement(e);
        if (*res != Eval::SExpr(Eval::Undefined{})) cout << res->toString() << endl;
        pool.clear();
      } catch (Eval::EvalError& ex) {
        const auto& [found, prefix] = ex.e->toStringUntil(ex.at);
        cout << endl;
        if (found) {
          cout << "× Error evaluating, " << ex.what() << endl;
          cout << "| " << endl;
          cout << "| " << ex.e->toString() << endl;
          cout << "| " << std::string(prefix.size(), ' ')
                       << std::string(ex.at->toString().size(), '~') << endl;
        } else {
          cout << "× Error evaluating, " << ex.what() << endl;
          cout << "  At: " << ex.at->toString() << endl;
          cout << "  In: " << ex.e->toString() << endl;
        }
        cout << endl;
      }
    }
  }

private:
  Allocator<Eval::SExpr> pool;
  Eval::Environment env;
};

// See: https://stackoverflow.com/questions/116038/how-do-i-read-an-entire-file-into-a-stdstring-in-c
string readFile(std::ifstream&& in) {
  std::ostringstream sstr;
  sstr << in.rdbuf();
  return sstr.str();
}

int main() {
  Lisp interpreter;

  while (true) {
    string in;
    cout << ">> ";
    std::getline(cin, in);
    if (in.starts_with(':')) {
      in = in.substr(1);
      /* if (in.starts_with("reset")) { // Reset state
        in = in.substr(5);
        interpreter.reset();
      } else */ if (in.starts_with('{')) { // Multi-line input
        in = in.substr(1);
        string curr;
        std::getline(cin, curr);
        while (curr != ":}") {
          in += curr;
          std::getline(cin, curr);
        }
      } else if (in.starts_with("load")) { // Load file
        in = in.substr(4);
        while (in.starts_with(' ')) in = in.substr(1);
        in = readFile(std::ifstream(in));
      }
    }
    interpreter.evalPrint(in);
  }

  return 0;
}
