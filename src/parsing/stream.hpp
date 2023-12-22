#ifndef APIMU_PARSING_STREAM_HPP
#define APIMU_PARSING_STREAM_HPP

#include <string>
#include "basic.hpp"

namespace apimu::parsing {
#include "macros_open.hpp"

  // A class is a (finite) "revertable stream" of `T` if...
  template <typename T>
  class IStream {
    interface(IStream);
  public:
    // It allows generating the next element (or empty if reached the end):
    virtual auto advance() -> std::optional<T> = 0;
    // It allows obtaining the current position:
    virtual auto position() const -> size_t = 0;
    // It allows reverting to a previous position (i.e. `0 <= i <= position()`):
    virtual auto revert(size_t i) -> void = 0;
  };

  // A "buffered stream" copy-stores all generated elements, so as to avoid repeated calls to `advance()`.
  template <typename T>
  class IBufferedStream: public IStream<T> {
    interface(IBufferedStream);
  public:
    // It allows invalidating its cache past the current position
    // (in context-dependent parsing, this might be necessary before changing syntax):
    virtual auto invalidate() -> void = 0;
  };

  // A class is a "marked stream" of `T` if it is a "revertable stream" of `T`, and...
  template <typename T>
  class IMarkedStream: public IStream<T> {
    interface(IMarkedStream);
  public:
    // It allows adding a "mark" to the stream:
    virtual auto mark() -> void = 0;
    // It allows advancing the underlying stream without inserting a mark:
    virtual auto next() -> std::optional<T> = 0;
    // It allows clearing all markings:
    virtual auto clear() -> void = 0;
    // ...and `advance()` is implemented in term of them:
    auto advance() -> std::optional<T> final {
      auto const res = next();
      mark();
      return res;
    }
  };

  // A class is a "character stream" if it is a "revertable stream" of `Char`, and...
  class ICharStream: public IStream<Char> {
    interface(ICharStream);
  public:
    // It allows for obtaining a view of the whole string:
    virtual auto string() const -> std::string_view required;
    // It allows for obtaining a view of some substring:
    virtual auto slice(size_t start, size_t end) const -> std::string_view required;
  };

  // Simplest implementation of `IBufferedStream`.
  // Its underlying stream must not be modified elsewhere.
  template <typename T>
  class BufferedStream: public IBufferedStream<T> {
  public:
    explicit BufferedStream(IStream<T>& stream):
        _underlying(stream),
        _offset(stream.position()) {}

    auto advance() -> std::optional<T> override {
      assert(_position <= _buffer.size());
      if (_position == _buffer.size())
        _buffer.push_back(_underlying.advance());
      // Mid: _position < _elements.size()
      return _buffer[_position++];
    }
    auto position() const -> size_t override {
      return _position;
    }
    auto revert(size_t i) -> void override {
      assert(i <= _position), _position = i;
    }
    auto invalidate() -> void override {
      assert(_position <= _buffer.size());
      _underlying.revert(_offset + _position);
      _buffer.resize(_position);
    }

  private:
    IStream<T>& _underlying;               // Underlying stream.
    size_t const _offset;                  // Initial offset.
    size_t _position = 0;                  // Current position = index in `_buffer`.
    std::vector<std::optional<T>> _buffer; // Stored elements.
  };

  // Simplest implementation of `IMarkedStream`.
  // Its underlying stream must not be modified elsewhere (exception: `underlying.advance()` is permitted;
  // effect is the same as calling `next()`).
  template <typename T>
  class MarkedStream: public IMarkedStream<T> {
  public:
    explicit MarkedStream(IStream<T>& stream):
        _underlying(stream),
        _offset(stream.position()) {}

    auto position() const -> size_t override {
      return _offsets.size();
    }
    auto revert(size_t i) -> void override {
      assert(i <= _offsets.size());
      _offsets.resize(i);
      _underlying.revert(_offsets.empty() ? _offset : _offsets.back());
    }
    auto mark() -> void override {
      _offsets.push_back(_underlying.position());
    }
    auto next() -> std::optional<T> override {
      return _underlying.advance();
    }
    auto clear() -> void override {
      _offset = _underlying.position(), _offsets.clear();
    }

  private:
    IStream<T>& _underlying;      // Underlying stream.
    size_t _offset;               // Initial offset.
    std::vector<size_t> _offsets; // Offsets of marks.
  };

  // Simplest implementation of `ICharStream` (wrapper around a `std::string`).
  class CharStream: public ICharStream {
  public:
    explicit CharStream(std::string string):
        _string(std::move(string)) {}

    auto advance() -> std::optional<Char> override {
      if (_position >= _string.size())
        return {};
      return static_cast<Char>(_string[_position++]);
    }
    auto position() const -> size_t override {
      return _position;
    }
    auto revert(size_t i) -> void override {
      assert(i <= _position), _position = i;
    }

    auto string() const -> std::string_view override {
      return _string;
    }
    auto slice(size_t start, size_t end) const -> std::string_view override {
      assert(start <= end && end <= _position);
      return std::string_view(_string).substr(start, end - start);
    }

  private:
    std::string _string;  // Underlying string.
    size_t _position = 0; // Current position.
  };

#include "macros_close.hpp"
}

#endif // APIMU_PARSING_STREAM_HPP
