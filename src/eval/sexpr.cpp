#include "sexpr.hpp"


namespace Eval {

  using std::string, std::pair, std::make_pair;
  using std::get, std::holds_alternative, std::visit;


  SExpr* SExpr::clone(Core::Allocator<SExpr>& pool) const {
    return visit(Matcher{
      [&] (Nil)               { return pool.emplaceBack(Nil{}); },
      [&] (Cons const& cons)  { return pool.emplaceBack(cons.head->clone(pool), cons.tail->clone(pool)); },
      [&] (Symbol const& sym) { return pool.emplaceBack(sym); },
      [&] (Number const& num) { return pool.emplaceBack(num); },
      [&] (String const& str) { return pool.emplaceBack(str); },
      [&] (Boolean boolean)   { return pool.emplaceBack(boolean); },
      [&] (Undefined)         { return pool.emplaceBack(Undefined{}); },
      [&] (Closure const&)    { throw Core::NotImplemented();
                                return pool.emplaceBack(Undefined{}); }
    }, v);
  }

  string SExpr::toString() const {
    return toStringUntil(nullptr).second;
  }

  pair<bool, string> SExpr::toStringUntil(const SExpr* p) const {
    if (this == p) return make_pair(true, "");
    return visit(Matcher{
      []  (Nil)               { return make_pair(false, string("()")); },
      [p] (Cons const& cons)  {
        string res = "(";
        const auto& [f0, s0] = cons.head->toStringUntil(p);
        res += s0; if (f0) return make_pair(true, res);
        const SExpr* q = cons.tail;
        while (holds_alternative<Cons>(q->v)) {
          const auto& [hd, tl] = get<Cons>(q->v);
          res += " "; if (q == p) return make_pair(true, res);
          const auto& [f1, s1] = hd->toStringUntil(p);
          res += s1; if (f1) return make_pair(true, res);
          q = tl;
        }
        if (!holds_alternative<Nil>(q->v)) {
          res += " . "; if (q == p) return make_pair(true, res);
          const auto& [f2, s2] = q->toStringUntil(p);
          res += s2; if (f2) return make_pair(true, res);
        }
        if (q == p) return make_pair(true, res);
        return make_pair(false, res + ")");
      },
      []  (Symbol const& sym) { return make_pair(false, sym.s); },
      []  (Number const& num) { return make_pair(false, std::to_string(num)); },
      []  (String const& str) { return make_pair(false, "\"" + escapeString(str) + "\""); },
      []  (Boolean boolean)   { return make_pair(false, string(boolean? "#true" : "#false")); },
      []  (Undefined)         { return make_pair(false, string("#undefined")); },
      []  (Closure const& cl) { return make_pair(false, string("#<params: " + cl.formal->toString() + ", body: " + cl.es->toString() + "...>")); }
    }, v);
  }

  string SExpr::escapeString(const string& s) {
    string res;
    for (char c: s) {
      switch (c) {
        case '"': res += "\\\""; break;
        case '\\': res += "\\\\"; break;
        case '\a': res += "\\a"; break;
        case '\b': res += "\\b"; break;
        case '\f': res += "\\f"; break;
        case '\n': res += "\\n"; break;
        case '\r': res += "\\r"; break;
        case '\t': res += "\\t"; break;
        case '\v': res += "\\v"; break;
        default: res += c; break;
      }
    }
    return res;
  }

  string SExpr::unescapeString(const string& s) {
    string res;
    for (size_t i = 0; i < s.size(); i++) {
      if (s[i] == '\\' && i + 1 < s.size()) {
        char c = s[i + 1];
        switch (c) {
          case '\'': res += '\''; break;
          case '"': res += '"'; break;
          case '?': res += '?'; break;
          case '\\': res += '\\'; break;
          case 'a': res += '\a'; break;
          case 'b': res += '\b'; break;
          case 'f': res += '\f'; break;
          case 'n': res += '\n'; break;
          case 'r': res += '\r'; break;
          case 't': res += '\t'; break;
          case 'v': res += '\v'; break;
          default: res += '\\'; res += c; break;
        }
        i++;
        continue;
      }
      res += s[i];
    }
    return res;
  }

}
