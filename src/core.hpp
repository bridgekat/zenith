// ApiMu/FOL verifier v0.1 (C++ version)
// Licensed under Creative Commons CC0 (no copyright reserved, use at your will)

// This variant of FOL & ND is largely based on Dirk van Dalen's *Logic and Structure*...
// Additional features are described in `../notes/design.md`.

// This is much more efficient compared to the Haskell version, but can be harder to read, and may contain (many) errors.
// Currently it does not support "private" and "undef".
// (I will need a parser and a pretty-printer to properly debug it...)

#ifndef CORE_HPP_
#define CORE_HPP_

// The `core` folder contains everything related to the verifier:

// By class:
#include "core/base.hpp"    // Allocator...
#include "core/context.hpp" // Type, Context...
#include "core/expr.hpp"    // Expr...
#include "core/proof.hpp"   // Proof, Decl...

// By functionality:
// - Formation/typing rules are in `core/expr.cpp`
// - Context-changing rules are in `core/context.cpp`
// - Non-context-changing and definition rules are in `core/proof.cpp`

#endif // CORE_HPP_
