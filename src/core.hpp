#ifndef CORE_HPP_
#define CORE_HPP_

// The `core` folder contains everything related to the verifier (excluding definitions):

#include "core/base.hpp"    // Allocator, Unreachable, NotImplemented, NonExhaustive
#include "core/context.hpp" // Context
#include "core/expr.hpp"    // Expr, InvalidExpr
#include "core/fol/fol.hpp" // FOLContext, FOLForm (utility functions that work with first-order logic formulas)

#endif // CORE_HPP_
