#include <iostream>
#include <string>
#include "core.hpp"
#include "eval/sexpr.hpp"
#include "eval/environment.hpp"

using std::string;
using std::cin, std::cout, std::endl;
using namespace Core;
using namespace Eval;


int main() {

  #define e(...)     pool.emplaceBack(__VA_ARGS__)
  #define nil        e(Nil{})
  #define cons(a, b) e(a, b)

  {
    Allocator<SExpr> pool;
    Environment env;
    
    SExpr* ex = cons(e(Symbol{ "if" }), cons(cons(e(Symbol{ "null?" }), cons(cons(e(Symbol{ "quote" }), cons(cons(e(1), nil), nil)), nil)), cons(e(0), cons(e(1), nil))));
    cout << ex->toString() << endl;

    ex = cons(e(Symbol{ "+" }), cons(e(1), cons(e(2), cons (e(3), nil))));
    cout << ex->toString() << endl;
    cout << env.eval(ex)->toString() << endl;
  }

  return 0;
}
