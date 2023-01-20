// Parsing :: Char, Symbol, Precedence, Stream...

#ifndef STREAM_HPP_
#define STREAM_HPP_

#include <deque>
#include <limits>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
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

  /*
  // `G` is a "revertable stream" of `T` if...
  template <typename G, typename T>
  concept Stream = requires (G g, G const& cg, size_t i) {
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

  // A class is a "revertable stream" of `T` if...
  template <typename T>
  class Stream {
    interface(Stream);
  public:
    // It allows checking if there are no more elements:
    virtual auto eof() const -> bool required;
    // It allows generating the next element;
    virtual auto advance() -> T required;
    // It allows obtaining the current position (which must be zero initially):
    virtual auto position() const -> size_t required;
    // It allows reverting to a previous position (i.e. `0 <= i <= position()`):
    virtual auto revert(size_t i) -> void required;
  };

  // Simple wrapper around a `std::string`.
  class CharStream: public Stream<Char> {
  public:
    // A `CharBuffer` is constructed from a `std::string`.
    explicit CharStream(std::string string):
      _string(std::move(string)) {}

    auto eof() const -> bool override { return _position == _string.size(); }
    auto advance() -> Char override { return _position < _string.size() ? static_cast<Char>(_string[_position++]) : 0; }
    auto position() const -> size_t override { return _position; }
    auto revert(size_t i) -> void override { assert(i <= _position), _position = i; }

    // Returns whole string.
    auto string() -> std::string_view { return _string; }

    // Returns a substring.
    auto slice(size_t start, size_t end) -> std::string_view {
      assert(start <= end && end <= _position);
      return std::string_view(_string).substr(start, end - start);
    }

  private:
    size_t _position = 0;
    std::string _string;
  };

  // A `LookaheadStream` that works with a "revertable stream".
  // It copy-stores all generated elements, so as to avoid repeated work.
  template <typename T>
  class LookaheadStream: public Stream<T> {
  public:
    // A `LookaheadStream` is constructed from a "revertable stream" of `T`.
    // Given reference must be valid over the `LookaheadStream`'s lifetime.
    explicit LookaheadStream(Stream<T>& stream):
      _stream(stream),
      _offset(stream.position()) {}

    auto eof() const -> bool override { return _position == _elements.size() && _stream.eof(); }
    auto advance() -> T override {
      assert(_position <= _elements.size());
      if (_position == _elements.size()) _elements.push_back(_stream.advance());
      // Mid: _position < _elements.size()
      return _elements[_position++];
    }
    auto position() const -> size_t override { return _position; }
    auto revert(size_t i) -> void override { assert(i <= _position), _position = i; }

    // Invalidates cache past the current position (inclusive).
    auto invalidate() -> void {
      assert(_position <= _elements.size());
      _stream.revert(_offset + _position);
      _elements.resize(_position);
    }

  private:
    Stream<T>& _stream;
    size_t _offset;
    size_t _position = 0;
    std::deque<T> _elements;
  };
}

#endif // STREAM_HPP_
