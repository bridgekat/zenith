// Parsing :: Char, Symbol, Precedence, Token

#ifndef PARSING_BASIC_HPP_
#define PARSING_BASIC_HPP_

#include <limits>
#include <optional>
#include <string_view>
#include <common.hpp>

namespace Parsing {

  // Assuming 8-bit code units (UTF-8).
  using Char = uint8_t;
  constexpr auto CharMax = std::numeric_limits<Char>::max();

  // Unified ID for terminal and nonterminal symbols.
  using Symbol = uint32_t;
  constexpr auto SymbolMax = std::numeric_limits<Symbol>::max();

  // Operator precedence levels.
  using Precedence = uint16_t;
  constexpr auto PrecedenceMax = std::numeric_limits<Precedence>::max();

  // A token emitted by a lexer.
  struct Token {
    std::optional<Symbol> id; // Terminal symbol ID (empty if unrecognised).
    std::string_view lexeme;  // Lexeme. `lexeme.size() == end - begin`.
    size_t begin;             // Start index in original character stream.
    size_t end;               // End index in original character stream.
  };

}

#endif // PARSING_BASIC_HPP_
