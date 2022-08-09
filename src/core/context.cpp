#include "context.hpp"
#include "expr.hpp"

namespace Core {

  using std::string;
  using std::vector;

  Context::Context(): pools(), entries(), indices() { pools.emplace_back(); }

  size_t Context::addDefinition(const string& s, const Expr* e) {
    e->checkType(*this, temp());
    entries.emplace_back(s, e->reduce(temp())->clone(pools.back()));
    return entries.size() - 1;
  }

  size_t Context::pushAssumption(const string& s, const Expr* e) {
    e->checkType(*this, temp());
    pools.emplace_back();
    entries.emplace_back(s, e->reduce(temp())->clone(pools.back()));
    indices.push_back(entries.size() - 1);
    return entries.size() - 1;
  }

  // Context-changing rules (implies/forall-intro) & definition generalization rules here
  bool Context::pop() {
    using enum Expr::VarTag;
    using enum Expr::PiTag;

    if (indices.empty() || pools.size() < 2) return false;
    auto& pool1 = pools[pools.size() - 1]; // To be deallocated, can be used as a temporary pool
    auto& pool2 = pools[pools.size() - 2];
    const size_t index = indices.back();
    const auto [s, x] = entries[index];

#define expr(...) Expr::make(pool2, __VA_ARGS__)

    // Add abstractions over the hypothesized variable, copying all expressions from `pool1` to `pool2`
    // Make bound + remap index
    auto modify = [&pool2, index](uint64_t n, const Expr* x) -> const Expr* {
      if (x->var.tag == VFree && x->var.id == index) return expr(VBound, n);
      if (x->var.tag == VFree && x->var.id > index) return expr(expr(VFree, x->var.id - 1), expr(VBound, n));
      return x->clone(pool2);
    };

    // Alter types
    for (size_t i = index; i + 1 < entries.size(); i++) {
      const auto& [t, y] = entries[i + 1];
      entries[i] = {t, expr(PPi, s, x->clone(pool2), y->updateVars(modify, pool1)->clone(pool2))};
    }
    entries.pop_back();

    // Should never throw, for debugging only
    for (size_t i = index; i < entries.size(); i++) {
      try {
        entries[i].second->checkType(*this, pool1);
      } catch (InvalidExpr&) { unreachable; }
    }

#undef expr

    indices.pop_back();
    pools.pop_back();
    return true;
  }

}
