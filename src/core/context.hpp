// Core :: Context

#ifndef CONTEXT_HPP_
#define CONTEXT_HPP_

#include <vector>
#include <string>
#include <utility>
#include <optional>
#include "base.hpp"


namespace Core {

  class Expr;

  // The context is stored as a stack (an std::vector whose last element denotes the topmost layer).
  // Here, "assumed" and "defined" entries are interleaved, stored linearly in one array.
  // Invariant: all entries are in beta-reduced form, and are stored in an allocator managed by this `Context`.
  class Context {
  public:
    Context();

    // Add variable unconditionally (for axioms/definitions)
    size_t addDefinition(const std::string& s, const Expr* e);

    // Add variable as assumption
    size_t pushAssumption(const std::string& s, const Expr* e);

    // Pops last assumption, performing appropriate changes to all variables in the top layer.
    // Returns false if there is no assumptions left.
    bool pop();

    size_t size() const { return entries.size(); }
    const Expr* operator[](size_t index) const { return entries.at(index).second; }
    std::string identifier(size_t index) const { return entries.at(index).first; }

    // Look up by literal name (slow, not commonly used)
    std::optional<size_t> lookup(const std::string& s) const {
      // Unsigned count down: https://nachtimwald.com/2019/06/02/unsigned-count-down/
      for (size_t i = entries.size(); i --> 0;) if (entries[i].first == s) return i;
      return std::nullopt;
    }
  
  protected:
    // Allocators
    std::vector<Allocator<Expr>> pools;
    // All entries
    std::vector<std::pair<std::string, const Expr*>> entries;
    // Indices of "assumed" entries
    std::vector<size_t> indices;
  };

}

#endif // CONTEXT_HPP_
