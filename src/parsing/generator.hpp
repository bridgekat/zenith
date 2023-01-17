// Parsing :: Char, Symbol, Precedence, Token, Generator, LookaheadBuffer...

#ifndef GENERATOR_HPP_
#define GENERATOR_HPP_

#include <deque>
#include <limits>
#include <optional>
#include <string>
#include <string_view>
#include <common.hpp>

namespace Parsing {

  // Assuming 8-bit code units (UTF-8).
  using Char = uint8_t;
  constexpr auto CharMax = std::numeric_limits<Char>::max();

  // Unified ID for terminal and nonterminal symbols.
  using Symbol = uint32_t;

  // Operator precedence levels.
  using Precedence = uint16_t;
  constexpr auto PrecedenceMax = std::numeric_limits<Precedence>::max();

  // A token emitted by a lexer.
  struct Token {
    Symbol id;               // Terminal symbol ID.
    size_t startPos;         // Start index in original string.
    size_t endPos;           // End index in original string.
    std::string_view lexeme; // Lexeme. `lexeme.size() == endPos - startPos`.
  };

  /*
  // `G` is a "revertable generator" of `T` if...
  template <typename G, typename T>
  concept Generator = requires (G g, G const& cg, size_t i) {
    // It allows checking if there are no more elements:
    { cg.eof() } -> std::convertible_to<bool>;
    // It allows generating the next element:
    { g.advance() } -> std::convertible_to<T>;
    // It allows obtaining the current position (which must be zero initially):
    { cg.position() } -> std::convertible_to<size_t>;
    // It allows reverting to a previous position (i.e. `0 <= i <= position()`):
    g.revert(i);
  };
  */

  // A class is a "revertable generator" of `T` if...
  template <typename T>
  class Generator {
  public:
    virtual ~Generator() {}
    // It allows checking if there are no more elements:
    virtual auto eof() const -> bool pure_virtual;
    // It allows generating the next element;
    virtual auto advance() -> T pure_virtual;
    // It allows obtaining the current position (which must be zero initially):
    virtual auto position() const -> size_t pure_virtual;
    // It allows reverting to a previous position (i.e. `0 <= i <= position()`):
    virtual auto revert(size_t i) -> void pure_virtual;
  };

  // Simple wrapper around a `std::string`.
  class CharBuffer: public Generator<Char> {
  public:
    // A `CharBuffer` is constructed from a `std::string`.
    explicit CharBuffer(std::string const& string):
      _string(string) {}

    auto eof() const -> bool override { return _position == _string.size(); }
    auto advance() -> Char override { return _position < _string.size() ? static_cast<Char>(_string[_position++]) : 0; }
    auto position() const -> size_t override { return _position; }
    auto revert(size_t i) -> void override { assert_always(i <= _position), _position = i; }

    // Returns whole string.
    auto string() -> std::string_view { return _string; }

    // Returns a substring.
    auto slice(size_t start, size_t end) -> std::string_view {
      assert_always(start <= end && end <= _position);
      return std::string_view(_string).substr(start, end - start);
    }

  private:
    size_t _position = 0;
    std::string _string;
  };

  // A `LookaheadBuffer` that works with a "revertable generator".
  // It copy-stores all generated elements, so as to avoid repeated work.
  template <typename T>
  class LookaheadBuffer: public Generator<T> {
  public:
    // A `LookaheadBuffer` is constructed from a "revertable generator" of `T`.
    explicit LookaheadBuffer(Generator<T>* generator):
      _generator(generator) {}

    auto eof() const -> bool override { return _position == _elements.size() && _generator->eof(); }
    auto advance() -> T override {
      if (_position >= _elements.size()) {
        assert_always(_position == _elements.size());
        _elements.push_back(_generator->advance());
      }
      // Mid: _position < _elements.size()
      return _elements[_position++];
    }
    auto position() const -> size_t override { return _position; }
    auto revert(size_t i) -> void override { assert_always(i <= _position), _position = i; }

    // Invalidates cache past the current position (inclusive).
    auto invalidate() -> void { _elements.resize(_position); }

  private:
    Generator<T>* _generator;
    size_t _position = 0;
    std::deque<T> _elements;
  };

  // inline auto example1 = CharBuffer("233");
  // inline auto example2 = LookaheadBuffer(&example1);
}

#endif // GENERATOR_HPP_
