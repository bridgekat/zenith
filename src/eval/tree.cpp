#include "tree.hpp"
#include <sstream>

using std::string;
using std::pair;

namespace apimu::eval {
#include "macros_open.hpp"

  auto Tree::clone(Allocator<Tree>& pool, Tree* nil, Tree* unit) const -> Tree* {
    return match(
      *this,
      [&](Nil const&) { return nil; },
      [&](Cons const& x) { return pool.make(x.head->clone(pool, nil, unit), x.tail->clone(pool, nil, unit)); },
      [&](Symbol const& x) { return pool.make(x); },
      [&](Prim const& x) { return pool.make(x); },
      [&](Nat64 const& x) { return pool.make(x); },
      [&](String const& x) { return pool.make(x); },
      [&](Bool const& x) { return pool.make(x); },
      [&](Unit const&) { return unit; },
      [&](Closure const&) -> Tree* { unimplemented; },
      [&](Native const& x) { return pool.make(x); }
    );
  }

  auto Tree::toString() const -> string { return toStringUntil(nullptr).second; }

  auto Tree::toStringUntil(Tree const* p) const -> pair<bool, string> {
    if (this == p) return {true, ""};
    return match(
      *this,
      [](Nil const&) { return pair(false, string("()")); },
      [p](Cons const& x) {
        auto res = string("(");
        auto const& [f0, s0] = x.head->toStringUntil(p);
        res += s0;
        if (f0) return pair(true, res);
        auto q = x.tail;
        while (auto cons = get_if<Cons>(q)) {
          auto const& [hd, tl] = *cons;
          res += " ";
          if (q == p) return pair(true, res);
          auto const& [f1, s1] = hd->toStringUntil(p);
          res += s1;
          if (f1) return pair(true, res);
          q = tl;
        }
        if (!get_if<Nil>(q)) {
          res += " . ";
          if (q == p) return pair(true, res);
          auto const& [f2, s2] = q->toStringUntil(p);
          res += s2;
          if (f2) return pair(true, res);
        }
        if (q == p) return pair(true, res);
        return pair(false, res + ")");
      },
      [](Symbol const& x) { return pair(false, x.val); },
      [](Prim const& x) { return pair(false, "#<primitive " + std::to_string(x.id) + ">"); },
      [](Nat64 const& x) { return pair(false, std::to_string(x.val)); },
      [](String const& x) { return pair(false, "\"" + escapeString(x.val) + "\""); },
      [](Bool const& x) { return pair(false, string(x.val ? "#true" : "#false")); },
      [](Unit const&) { return pair(false, string("#unit")); },
      [](Closure const& x) {
        return pair(false, "#<closure params: " + x.formal->toString() + ", body: " + x.es->toString() + "...>");
      },
      [](Native const& x) {
        auto addr = std::stringstream();
        addr << &x.val;
        return pair(false, "#<native type: " + string(x.val.type().name()) + ", addr: " + addr.str() + ">");
      }
    );
  }

  auto Tree::escapeString(string const& s) -> string {
    auto res = string();
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

  auto Tree::unescapeString(string const& s) -> string {
    auto res = string();
    for (auto i = 0_z; i < s.size(); i++) {
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

#include "macros_close.hpp"
}
