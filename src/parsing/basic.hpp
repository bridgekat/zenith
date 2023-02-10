#ifndef APIMU_PARSING_BASIC_HPP
#define APIMU_PARSING_BASIC_HPP

#include <limits>
#include <optional>
#include <string_view>
#include <common.hpp>

namespace apimu::parsing {
#include "macros_open.hpp"

  // Assuming 8-bit code units (UTF-8).
  using Char = uint8_t;
  constexpr Char CharMax = std::numeric_limits<Char>::max();

  // Unified ID for terminal and nonterminal symbols.
  using Symbol = uint32_t;
  constexpr Symbol SymbolMax = std::numeric_limits<Symbol>::max();

  // Operator precedence levels.
  using Precedence = uint32_t;
  constexpr Precedence PrecedenceMax = std::numeric_limits<Precedence>::max();

#include "macros_close.hpp"
}

#endif // APIMU_PARSING_BASIC_HPP
