#ifndef COMMON_HPP_
#define COMMON_HPP_

#include <concepts>
#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <iostream>
#include <memory>
#include <utility>
#include <variant>
#include <vector>

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

#undef assert

// Assertion that remains present under non-debug configurations.
inline auto assert(bool expr, char const* name, char const* file, int line, char const* func) -> void {
  if (!expr) {
    std::cerr << "Assertion failed: " << name << std::endl;
    unreachable(file, line, func);
  }
}

#define unreachable   unreachable(__FILE__, __LINE__, static_cast<char const*>(__func__))
#define unimplemented unimplemented(__FILE__, __LINE__, static_cast<char const*>(__func__))
#define assert(expr)  assert(expr, #expr, __FILE__, __LINE__, static_cast<char const*>(__func__))

// Compiler & tools support for literal suffix `uz` (in C++23) is still incomplete...
// See: https://en.cppreference.com/w/cpp/language/user_literal
constexpr auto operator"" _z(unsigned long long n) -> size_t { return n; }

// A binary hash function.
// See: https://stackoverflow.com/questions/2590677/how-do-i-combine-hash-values-in-c0x
template <typename T>
inline auto combineHash(size_t acc, T const& v) -> size_t {
  auto const hasher = std::hash<T>();
  return acc ^ (hasher(v) + 0x9e3779b9 + (acc << 6) + (acc >> 2)); // NOLINT(cppcoreguidelines-avoid-magic-numbers)
}

// Recursively combines hashes.
// All values must have types that are hashable by `std::hash`.
inline auto combineHashes(size_t acc) -> size_t { return acc; }
template <typename T, typename... Ts>
inline auto combineHashes(size_t acc, T const& v, Ts... args) -> size_t {
  return combineHashes(combineHash(acc, v), args...);
}

// Uses 0 as initial seed.
// All values must have types that are hashable by `std::hash`.
template <typename... Ts>
inline auto hashAll(Ts... args) -> size_t {
  return combineHashes(0, args...);
}

// Hash function for `std::pair`.
struct PairHasher {
  template <typename S, typename T>
  auto operator()(std::pair<S, T> const& p) const -> size_t {
    return hashAll(p.first, p.second);
  }
};

// "Pattern matching" on `std::variant`.
// See: https://en.cppreference.com/w/cpp/utility/variant/visit
// See: https://en.cppreference.com/w/cpp/language/aggregate_initialization
template <typename... Ts>
struct Matcher: Ts... {
  using Ts::operator()...;
};
template <typename T, typename... Ts>
constexpr auto match(T&& variant, Ts&&... lambdas) {
  return std::visit(Matcher<Ts...>{std::forward<Ts>(lambdas)...}, std::forward<T>(variant));
}

// Other "syntax enhancements".
#define required = 0

// See: https://softwareengineering.stackexchange.com/questions/235674/what-is-the-pattern-for-a-safe-interface-in-c
#define interface(T)                                 \
protected:                                           \
  T() noexcept = default;                            \
  T(T const&) noexcept = default;                    \
  T(T&&) noexcept = default;                         \
  auto operator=(T const&) noexcept -> T& = default; \
  auto operator=(T&&) noexcept -> T& = default;      \
public:                                              \
  virtual ~T() = default

// A simple region-based memory allocator (uses larger blocks than `std::deque`).
// This ensures that allocated objects stay in the same place, like in `std::deque`.
template <typename T>
class Allocator {
public:
  static constexpr size_t defaultBlockSize = 1024_z;

  Allocator(size_t _blockSize = defaultBlockSize):
    _blockSize(_blockSize) {}

  ~Allocator() noexcept { _deallocateBlocks(); }

  Allocator(Allocator const&) = delete;
  Allocator(Allocator&& r) noexcept:
    _blockSize(r._blockSize),
    _alloc(r._alloc),
    _blocks(std::move(r._blocks)),
    _next(r._next) {}

  auto operator=(Allocator const&) -> Allocator& = delete;
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
