#ifndef COMMON_HPP_
#define COMMON_HPP_

#include <cstddef>
#include <cstdint>
#include <iostream>
#include <memory>
#include <utility>
#include <vector>

// Syntax "enhancements".
#define pure_virtual = 0

// Make sure to put these into the global scope.
using std::int8_t;
using std::int16_t;
using std::int32_t;
using std::int64_t;
using std::ptrdiff_t;

using std::uint8_t;
using std::uint16_t;
using std::uint32_t;
using std::uint64_t;
using std::size_t;

// See: https://en.cppreference.com/w/cpp/language/user_literal
constexpr auto operator"" _z(unsigned long long n) -> size_t { return n; }

// "Unreachable" mark.
[[noreturn]] inline auto unreachable(char const* file, int line, char const* func) -> void {
  std::cerr << "\"Unreachable\" code was reached: " << file << ":" << line << ", at function " << func << std::endl;
  std::terminate();
}

// "Unimplemented" mark.
[[noreturn]] inline auto unimplemented(char const* file, int line, char const* func) -> void {
  std::cerr << "\"Unimplemented\" code was called: " << file << ":" << line << ", at function " << func << std::endl;
  std::terminate();
}

// Assertion that remain present under non-debug configurations.
inline auto assert_always(bool expr, char const* name, char const* file, int line, char const* func) -> void {
  if (!expr) {
    std::cerr << "Assertion failed: " << name << std::endl;
    unreachable(file, line, func);
  }
}

#define unreachable         unreachable(__FILE__, __LINE__, static_cast<char const*>(__func__))
#define unimplemented       unimplemented(__FILE__, __LINE__, static_cast<char const*>(__func__))
#define assert_always(expr) assert_always(expr, #expr, __FILE__, __LINE__, static_cast<char const*>(__func__))

// See: https://stackoverflow.com/questions/2590677/how-do-i-combine-hash-values-in-c0x
template <class T>
inline auto hash_combine(size_t seed, T const& v) -> size_t {
  return seed ^ (std::hash<T>()(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2));
}

// See: https://www.techiedelight.com/use-std-pair-key-std-unordered_map-cpp/
struct PairHasher {
  template <class S, class T>
  auto operator()(std::pair<S, T> const& pair) const -> size_t {
    return std::hash<S>()(pair.first) ^ std::hash<T>()(pair.second);
  }
};

// See: https://en.cppreference.com/w/cpp/utility/variant/visit
template <typename... Ts>
struct Matcher: Ts... {
  using Ts::operator()...;
};
template <typename... Ts>
Matcher(Ts...) -> Matcher<Ts...>;

// A simple region-based memory allocator: https://news.ycombinator.com/item?id=26433654
// This ensures that objects stay in the same place.
template <typename T>
class Allocator {
public:
  static constexpr size_t defaultBlockSize = 1024_z;

  Allocator(size_t _blockSize = defaultBlockSize):
    _blockSize(_blockSize) {}

  Allocator(Allocator&& r):
    _blockSize(r._blockSize),
    _alloc(r._alloc),
    _blocks(std::move(r._blocks)),
    _next(r._next) {}

  auto operator=(Allocator&& r) noexcept -> Allocator& {
    swap(*this, r);
    return *this;
  }

  friend auto swap(Allocator& l, Allocator& r) noexcept -> void {
    using std::swap;
    swap(l._blockSize, r._blockSize);
    swap(l._alloc, r._alloc);
    swap(l._blocks, r._blocks);
    swap(l._next, r._next);
  }

  ~Allocator() noexcept { _deallocateBlocks(); }

  auto reset() -> void {
    _deallocateBlocks();
    _blocks.clear();
    _next = 0;
  }

  template <typename... Ts>
  auto emplace(Ts&&... args) -> T* {
    if (_next == 0) _blocks.push_back(_alloc.allocate(_blockSize));
    auto const res = _blocks.back() + _next;
    std::construct_at(res, std::forward<Ts>(args)...);
    _next++;
    if (_next >= _blockSize) _next = 0;
    return res;
  }

  auto add(T const& obj) -> T* { return emplace(obj); }

  auto size() const -> size_t {
    if (_next == 0) return _blockSize * _blocks.size();
    return _blockSize * (_blocks.size() - 1) + _next;
  }

private:
  size_t _blockSize;
  std::allocator<T> _alloc;
  std::vector<T*> _blocks;
  size_t _next = 0;

  auto _deallocateBlocks() -> void {
    for (auto i = 0_z; i < _blocks.size(); i++) {
      std::destroy_n(_blocks[i], (i + 1 == _blocks.size() && _next > 0) ? _next : _blockSize);
      _alloc.deallocate(_blocks[i], _blockSize);
    }
  }
};

#endif // COMMON_HPP_
