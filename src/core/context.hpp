// Core :: Sort, Type, Context

#ifndef CONTEXT_HPP_
#define CONTEXT_HPP_

#include <cstdint>
#include <vector>
#include <string>
#include <utility>
#include <optional>
#include "base.hpp"


namespace Core {

  class Expr;

  // The context is stored as a stack (an std::vector whose last element denotes the topmost layer).
  // Here, "assumed" and "defined" entries are interleaved, stored linearly in one array.
  class Context {
  public:
    // Pre-defined logical constants in a second-order language
    // Code consistency (checked at runtime): if you change this, you may have to update `Context::Context()`.
    enum Constant: uint64_t {
      SetVar, Initial, Equals, True, False, Not, And, Or, Implies, Iff, Forall, Exists, Unique,
      // ForallFunc,
      // ForallPred = ForallFunc + 256
    };

    // All entries
    std::vector<Allocator<Expr>> pools;
    std::vector<std::pair<std::string, const Expr*>> entries;
    // Indices of "assumed" entries
    std::vector<uint64_t> indices;

    // Built-in constants are inserted during initialization
    Context();

    // Add entries...
    size_t addDefinition(const std::string& s, const Expr* e);
    size_t pushAssumption(const std::string& s, const Expr* e);
    // Pops the last "assumed" entry, performs appropriate changes to all definitions and theorems in the top layer,
    // storing the new expressions in `pool`.
    // Returns false if there is no "assumed" entry left.
    bool pop();

    // Look up by index.
    // Use `valid(i)` to perform bound checks before accessing, and throw appropriate exception if index is too large.
    size_t size() const { return entries.size(); }
    bool valid(size_t index) const { return index < entries.size(); }
    const Expr* operator[](size_t index) const { return entries.at(index).second; }
    std::string nameOf(size_t index) const { return entries.at(index).first; }

    // Look up by literal name. (Slow, not commonly used)
    std::optional<uint64_t> lookup(const std::string& s) const {
      // Unsigned count down: https://nachtimwald.com/2019/06/02/unsigned-count-down/
      for (uint64_t i = static_cast<uint64_t>(entries.size()); i --> 0;) if (entries[i].first == s) return i;
      return std::nullopt;
    }
  };

}

#endif // CONTEXT_HPP_
