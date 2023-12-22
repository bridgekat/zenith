#ifndef APIMU_CORE_CONTEXT_HPP
#define APIMU_CORE_CONTEXT_HPP

#include <optional>
#include <string>
#include <utility>
#include <vector>
#include <common.hpp>

namespace apimu::core {
#include "macros_open.hpp"

  class Expr;

  // The context is stored as a stack (an std::vector whose last element denotes the topmost layer).
  // Here, "assumed" and "defined" entries are interleaved, stored linearly in one array.
  // Invariant: all entries are in beta-reduced form, and are stored in an allocator managed by this `Context`.
  class Context {
  public:
    Context();

    // Add variable unconditionally (for axioms/definitions)
    auto addDefinition(std::string const& s, Expr const* e) -> size_t;

    // Add variable as assumption
    auto pushAssumption(std::string const& s, Expr const* e) -> size_t;

    // Pops last assumption, performing appropriate changes to all variables in the top layer.
    // Returns false if there is no assumptions left.
    auto pop() -> bool;

    auto size() const -> size_t {
      return entries.size();
    }
    auto operator[](size_t index) const -> Expr const* {
      return entries.at(index).second;
    }
    auto identifier(size_t index) const -> std::string {
      return entries.at(index).first;
    }

    // Look up by literal name (slow, not commonly used)
    auto lookup(std::string const& s) const -> std::optional<size_t> {
      // Unsigned count down: https://nachtimwald.com/2019/06/02/unsigned-count-down/
      for (size_t i = entries.size(); i-- > 0;)
        if (entries[i].first == s)
          return i;
      return {};
    }

  protected:
    // Returns the top layer pool.
    auto pool() -> Allocator<Expr>& {
      return pools.back();
    }

  private:
    // Allocators
    std::vector<Allocator<Expr>> pools;
    // All entries
    std::vector<std::pair<std::string, Expr const*>> entries;
    // Indices of "assumed" entries
    std::vector<size_t> indices;
  };

#include "macros_close.hpp"
}

#endif // APIMU_CORE_CONTEXT_HPP
