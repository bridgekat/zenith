// Core :: Sort, Type, Context

#ifndef CONTEXT_HPP_
#define CONTEXT_HPP_

#include <vector>
#include <utility>
#include <string>
#include <variant>
#include <optional>
#include "base.hpp"


namespace Core {

  using std::vector;
  using std::pair, std::make_pair;
  using std::string;
  using std::variant, std::holds_alternative, std::get, std::monostate;
  using std::optional, std::make_optional, std::nullopt;


  // Possible "types" of expressions (ι means Var, * means Prop):
  //   Terms:      {{ 0, SVAR }}  (ι)
  //   Functions:  {{ k, SVAR }}  (ι → ... → ι → ι)
  //   Formulas:   {{ 0, SPROP }} (*)
  //   Predicates: {{ k, SPROP }} (ι → ... → ι → *)
  // Function/predicate schemas have "second-order parameters":
  //   {{ k1, s1 }, { k2, s2 }} means ((ι → ... → ι → s1) → ι → ... → ι → s2), etc.
  // (This is similar to Metamath definition checkers, according to Mario Carneiro!)

  enum class Sort: unsigned char { SVAR, SPROP };
  using enum Sort;
  typedef vector<pair<unsigned short, Sort>> Type;

  const Type TTerm    = {{ 0, SVAR }};
  const Type TFormula = {{ 0, SPROP }};

  string showType(const Type& t);

  class Expr;

  // The context is stored as a stack (an std::vector whose last element denotes the topmost layer).
  // Here, "assumed" and "defined" entries are interleaved, stored linearly in one array.
  class Context {
  public:
    // Context entry
    struct Entry {
      string name;
      variant<Type, const Expr*> info;
    };

    vector<Entry> a; // All entries
    vector<unsigned int> ind; // Indices of "assumed" entries
    const unsigned int eq;

    // Insert a built-in equality relation during initialization
    Context(): a(), ind(), eq(static_cast<unsigned int>(addDef("=", {{ 2, SPROP }}))) {}

    // Add entries...
    size_t addDef         (const string& s, const Type& t) { a.push_back(Entry{ s, t }); return a.size() - 1; }
    size_t addTheorem     (const string& s, const Expr* e) { a.push_back(Entry{ s, e }); return a.size() - 1; }
    size_t pushVar        (const string& s, const Type& t) { a.push_back(Entry{ s, t }); ind.push_back(a.size() - 1); return a.size() - 1; }
    size_t pushAssumption (const string& s, const Expr* e) { a.push_back(Entry{ s, e }); ind.push_back(a.size() - 1); return a.size() - 1; }
    // Pops the last "assumed" entry, performs appropriate changes to all definitions and theorems in the top layer,
    // storing the new expressions in `pool`.
    // Returns false if there is no "assumed" entry left.
    bool pop(Allocator<Expr>& pool);

    // Look up by index.
    // Use `valid(i)` to perform bound checks before accessing, and throw appropriate exception if index is too large.
    size_t size() const { return a.size(); }
    bool valid(size_t index) const { return index < a.size(); }
    const variant<Type, const Expr*>& operator[](size_t index) const { return a.at(index).info; }
    const string& nameOf(size_t index) const { return a.at(index).name; }

    // Look up by literal name. (Slow, not commonly used)
    optional<unsigned int> lookup(const string& s) const {
      // Unsigned count down: https://nachtimwald.com/2019/06/02/unsigned-count-down/
      for (unsigned int i = static_cast<unsigned int>(a.size()); i --> 0;)
        if (a[i].name == s) return i;
      return nullopt;
    }
  };

}

#endif // CONTEXT_HPP_
