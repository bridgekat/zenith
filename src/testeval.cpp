#include <iostream>
#include <string>
#include <vector>
#include "core.hpp"
#include "parsing/language.hpp"
#include "eval/sexpr.hpp"
#include "eval/environment.hpp"

using std::string;
using std::vector;
using std::cin, std::cout, std::endl;
using Core::Allocator;
using Parsing::ParseTree, Parsing::makePrec;
using namespace Eval;


// ===================
// Symbol declarations
// ===================

#define symbol(T) \
  struct T; \
  template <> struct Parsing::SymbolName<T> { \
    static const string get() { return #T; } \
  }; \
  struct T

#define assymbol(T) \
  template <> struct Parsing::SymbolName<T> { \
    static const string get() { return #T; } \
  }; \

// Terminal symbols

symbol(Blank) {};
symbol(LParen) {};
symbol(RParen) {};
symbol(LBracket) {};
symbol(RBracket) {};
symbol(Point) {};
symbol(Quote) {};
symbol(Comma) {};

assymbol(Symbol);
assymbol(Number);
assymbol(String);
assymbol(Boolean);
assymbol(Undefined);

// Nonterminal symbols

symbol(List) { SExpr* e; };
symbol(ListInner) { SExpr* e; };
symbol(SExprStar) { vector<SExpr*> es; }; // Zero or more `SExpr`s
symbol(SExprPlus) { vector<SExpr*> es; }; // One or more `SExpr`s
symbol(SExprSym) { SExpr* e; };

#undef symbol
#undef assymbol

class Lisp: public Parsing::Language {
public:

  // ====================================
  // Patterns, rules and semantic actions
  // ====================================

  Lisp(): pool(), env() {

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
    addPattern([] (const string& lexeme) -> String { return SExpr::unescapeString(lexeme.substr(1, lexeme.size() - 2)); },
      concat(ch('"'), star(alt(except('"', '\\'), concat(ch('\\'), ch('"', '\\', 'a', 'b', 'f', 'n', 'r', 't', 'v')))), ch('"')));
    addPattern([] (const string&) -> Boolean { return true; },  word("#t"));
    addPattern([] (const string&) -> Boolean { return false; }, word("#f"));
    addPattern([] (const string&) -> Undefined { return {}; },  word("#undefined"));

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

    addRule([]     (LParen, ListInner&& inner, RParen)     -> List { return { inner.e }; });
    addRule([]     (LBracket, ListInner&& inner, RBracket) -> List { return { inner.e }; });
    addRule([this] (SExprStar&& star)                      -> ListInner { return { makeList(star.es) }; });
    addRule([this] (SExprPlus&& plus, Point, SExprSym&& e) -> ListInner { return { makeList(plus.es, e.e) }; });
    addRule([]     ()                                      -> SExprStar { return { {} }; });
    addRule([]     (SExprStar&& star, SExprSym&& e)        -> SExprStar { star.es.push_back(e.e); return { star.es }; });
    addRule([]     (SExprSym&& e)                          -> SExprPlus { return { { e.e } }; });
    addRule([]     (SExprPlus&& plus, SExprSym&& e)        -> SExprPlus { plus.es.push_back(e.e); return { plus.es }; });

    addRule([]     (List&& list)                           -> SExprSym { return { list.e }; });
    addRule([this] (Symbol&& sym)                          -> SExprSym { return { pool.emplaceBack(sym) }; });
    addRule([this] (Number&& num)                          -> SExprSym { return { pool.emplaceBack(num) }; });
    addRule([this] (String&& str)                          -> SExprSym { return { pool.emplaceBack(str) }; });
    addRule([this] (Boolean&& boolean)                     -> SExprSym { return { pool.emplaceBack(boolean) }; });
    addRule([this] (Undefined)                             -> SExprSym { return { pool.emplaceBack(Undefined()) }; });
    addRule([this] (Quote, SExprSym&& e)                   -> SExprSym { return { makeList({ pool.emplaceBack(Symbol("quote")), e.e }) }; });
    addRule([this] (Comma, SExprSym&& e)                   -> SExprSym { return { makeList({ pool.emplaceBack(Symbol("unquote")), e.e }) }; });

  }

  SExpr* makeList(const vector<SExpr*> a, SExpr* tail = nullptr) {
    SExpr* res = tail? tail : pool.emplaceBack(Nil());
    for (auto it = a.rbegin(); it != a.rend(); it++) res = pool.emplaceBack(*it, res);
    return res;
  }

  // ====================
  // Read-eval-print loop
  // ====================

  void evalPrint(const string& str) {
    lexer.setString(str);
    while (!parser.eof()) {
      auto opt = Language::nextSentence<SExprSym>();
      for (auto& ex: Language::popParsingErrors()) {
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
      const SExpr* e = opt->e;
      try {
        const SExpr* res = env.evalStatement(e);
        if (*res != SExpr(Undefined())) cout << res->toString() << endl;
      } catch (EvalError& ex) {
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
          cout << "  Subexpression: " << ex.at->toString() << endl;
        }
        cout << endl;
      }
    }
  }

private:
  Allocator<SExpr> pool;
  Environment env;
};

int main() {
  Lisp lisp;

  while (true) {
    string in;
    cout << ">> ";
    std::getline(cin, in);
    if (in == "{") {
      in = "";
      string curr;
      std::getline(cin, curr);
      while (curr != "}") {
        in += curr;
        std::getline(cin, curr);
      }
    }
    lisp.evalPrint(in);
  }

  return 0;
}
