#include "context.hpp"
#include "expr.hpp"

using std::string;

namespace apimu::core {
#include "macros_open.hpp"

  Context::Context():
      pools(),
      entries(),
      indices() {
    pools.emplace_back();
  }

  auto Context::addDefinition(string const& s, Expr const* e) -> size_t {
    e->checkType(*this, temp());
    entries.emplace_back(s, e->reduce(temp())->clone(pools.back()));
    return entries.size() - 1;
  }

  auto Context::pushAssumption(string const& s, Expr const* e) -> size_t {
    e->checkType(*this, temp());
    pools.emplace_back();
    entries.emplace_back(s, e->reduce(temp())->clone(pools.back()));
    indices.push_back(entries.size() - 1);
    return entries.size() - 1;
  }

  // Context-changing rules (implies/forall-intro) & definition generalization rules here
  auto Context::pop() -> bool {
    using enum Expr::VarTag;
    using enum Expr::PiTag;

    if (indices.empty() || pools.size() < 2)
      return false;
    auto& pool1 = pools[pools.size() - 1]; // To be deallocated, can be used as a temporary pool
    auto& pool2 = pools[pools.size() - 2];
    auto const index = indices.back();
    auto const [s, x] = entries[index];

#define expr(...) pool2.make(__VA_ARGS__)
    // Add abstractions over the hypothesized variable, copying all expressions from `pool1` to `pool2`
    // Make bound + remap index
    auto modify = [&pool2, index](uint64_t n, Expr const* x) -> Expr const* {
      if (x->var.tag == VFree && x->var.id == index)
        return expr(VBound, n);
      if (x->var.tag == VFree && x->var.id > index)
        return expr(expr(VFree, x->var.id - 1), expr(VBound, n));
      return x->clone(pool2);
    };

    // Alter types
    for (size_t i = index; i + 1 < entries.size(); i++) {
      auto const& [t, y] = entries[i + 1];
      entries[i] = {t, expr(PPi, s, x->clone(pool2), y->updateVars(modify, pool1)->clone(pool2))};
    }
    entries.pop_back();

    // Should never throw, for debugging only
    for (size_t i = index; i < entries.size(); i++) {
      try {
        entries[i].second->checkType(*this, pool1);
      } catch (InvalidExpr&) {
        unreachable;
      }
    }
#undef expr

    indices.pop_back();
    pools.pop_back();
    return true;
  }

#include "macros_close.hpp"
}
