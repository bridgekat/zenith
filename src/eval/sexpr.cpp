#include "sexpr.hpp"


namespace Eval {

  using std::string;
  using std::get, std::holds_alternative, std::visit;


  SExpr* SExpr::clone(Core::Allocator<SExpr>& pool) const {
    return visit(Matcher{
      [&] (Nil)               { return pool.emplaceBack(Nil{}); },
      [&] (const Cons& cons)  { return pool.emplaceBack(cons.head->clone(pool), cons.tail->clone(pool)); },
      [&] (const Symbol& sym) { return pool.emplaceBack(sym); },
      [&] (const Number& num) { return pool.emplaceBack(num); },
      [&] (const String& str) { return pool.emplaceBack(str); },
      [&] (Boolean boolean)   { return pool.emplaceBack(boolean); },
      [&] (Undefined)         { return pool.emplaceBack(Undefined{}); }
    }, v);
  }

  std::string SExpr::toString() const {
    return visit(Matcher{
      [] (Nil)               { return string("()"); },
      [] (const Cons& cons)  {
        string res = "(" + cons.head->toString();
        const SExpr* p = cons.tail;
        while (holds_alternative<Cons>(p->v)) {
          const auto& [hd, tl] = get<Cons>(p->v);
          res += " " + hd->toString();
          p = tl;
        }
        if (!holds_alternative<Nil>(p->v)) res += " . " + p->toString();
        return res + ")";
      },
      [] (const Symbol& sym) { return sym.s; },
      [] (const Number& num) { return std::to_string(num); },
      [] (const String& str) { return "\"" + str + "\""; }, // TODO: escape
      [] (Boolean boolean)   { return string(boolean? "true" : "false"); },
      [] (Undefined)         { return string("undefined"); }
    }, v);
  }

}
