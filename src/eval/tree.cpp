#include "tree.hpp"
#include <sstream>

namespace Eval {

  using std::string, std::pair, std::make_pair;
  using std::get, std::holds_alternative, std::visit;

  Tree* Tree::clone(Core::Allocator<Tree>& pool, Tree* nil, Tree* unit) const {
    return visit(
      Matcher{
        [&](Nil) { return nil; },
        [&](Cons const& x) { return pool.emplaceBack(x.head->clone(pool, nil, unit), x.tail->clone(pool, nil, unit)); },
        [&](Symbol const& x) { return pool.emplaceBack(x); },
        [&](Prim const& x) { return pool.emplaceBack(x); },
        [&](Nat64 const& x) { return pool.emplaceBack(x); },
        [&](String const& x) { return pool.emplaceBack(x); },
        [&](Bool const& x) { return pool.emplaceBack(x); },
        [&](Unit const&) { return unit; },
        [&](Closure const&) -> Tree* { notimplemented; },
        [&](Native const& x) { return pool.emplaceBack(x); },
      },
      v
    );
  }

  string Tree::toString() const { return toStringUntil(nullptr).second; }

  pair<bool, string> Tree::toStringUntil(const Tree* p) const {
    if (this == p) return make_pair(true, "");
    return visit(
      Matcher{
        [](Nil) { return make_pair(false, string("()")); },
        [p](Cons const& x) {
          string res = "(";
          const auto& [f0, s0] = x.head->toStringUntil(p);
          res += s0;
          if (f0) return make_pair(true, res);
          const Tree* q = x.tail;
          while (holds_alternative<Cons>(q->v)) {
            const auto& [hd, tl] = get<Cons>(q->v);
            res += " ";
            if (q == p) return make_pair(true, res);
            const auto& [f1, s1] = hd->toStringUntil(p);
            res += s1;
            if (f1) return make_pair(true, res);
            q = tl;
          }
          if (!holds_alternative<Nil>(q->v)) {
            res += " . ";
            if (q == p) return make_pair(true, res);
            const auto& [f2, s2] = q->toStringUntil(p);
            res += s2;
            if (f2) return make_pair(true, res);
          }
          if (q == p) return make_pair(true, res);
          return make_pair(false, res + ")");
        },
        [](Symbol const& x) { return make_pair(false, x.val); },
        [](Prim const& x) { return make_pair(false, "#<primitive " + std::to_string(x.id) + ">"); },
        [](Nat64 const& x) { return make_pair(false, std::to_string(x.val)); },
        [](String const& x) { return make_pair(false, "\"" + escapeString(x.val) + "\""); },
        [](Bool const& x) { return make_pair(false, string(x.val ? "#true" : "#false")); },
        [](Unit const&) { return make_pair(false, string("#unit")); },
        [](Closure const& x) {
          return make_pair(false, "#<closure params: " + x.formal->toString() + ", body: " + x.es->toString() + "...>");
        },
        [](Native const& x) {
          std::stringstream addr;
          addr << &x.val;
          return make_pair(false, "#<native type: " + string(x.val.type().name()) + ", addr: " + addr.str() + ">");
        },
      },
      v
    );
  }

  string Tree::escapeString(const string& s) {
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

  string Tree::unescapeString(const string& s) {
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
          default:
            res += '\\';
            res += c;
            break;
        }
        i++;
        continue;
      }
      res += s[i];
    }
    return res;
  }

}
