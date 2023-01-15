// Core :: Allocator...

#ifndef BASE_HPP_
#define BASE_HPP_

#include <cstddef>
#include <cstdint>
#include <deque>
#include <iostream>
#include <memory>
#include <utility>
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

// Should be present in ISO C++23. Redefined due to `ms-vscode.cpptools` being unable to recognise the "uz" suffix.
// See: https://stackoverflow.com/questions/22346369/initialize-integer-literal-to-stdsize-t
// This definition should never be visible to the compiler, as user-defined literal suffixes without a
// leading underscore are considered ill-formed by the standard.
// See: https://en.cppreference.com/w/cpp/language/user_literal
#if __cpp_size_t_suffix < 202011L
constexpr auto operator"" uz(unsigned long long n) -> size_t { return n; }
#endif

// "Unreachable" mark.
[[noreturn]] inline auto unreachable(char const* file, int line, char const* func) -> void {
  std::cerr << "\"Unreachable\" code was reached: " << file << ":" << line << ", at function " << func << std::endl;
  std::terminate();
}
#define unreachable unreachable(__FILE__, __LINE__, static_cast<char const*>(__func__))

// "Unimplemented" mark.
[[noreturn]] inline auto unimplemented(char const* file, int line, char const* func) -> void {
  std::cerr << "\"Unimplemented\" code was called: " << file << ":" << line << ", at function " << func << std::endl;
  std::terminate();
}
#define unimplemented unimplemented(__FILE__, __LINE__, static_cast<char const*>(__func__))

namespace Core {

  // A simple region-based memory allocator: https://news.ycombinator.com/item?id=26433654
  // This ensures that objects stay in the same place.
  template <typename T>
  class Allocator {
  public:
    static constexpr size_t DefaultBlockSize = 1024uz;

    Allocator(size_t blockSize = DefaultBlockSize):
      blockSize(blockSize),
      alloc(),
      blocks(),
      next(0) {}

    Allocator(Allocator&& r):
      blockSize(r.blockSize),
      alloc(r.alloc),
      blocks(std::move(r.blocks)),
      next(r.next) {}

    auto operator=(Allocator&& r) noexcept -> Allocator& {
      swap(*this, r);
      return *this;
    }

    friend auto swap(Allocator& l, Allocator& r) noexcept -> void {
      using std::swap;
      swap(l.blockSize, r.blockSize);
      swap(l.alloc, r.alloc);
      swap(l.blocks, r.blocks);
      swap(l.next, r.next);
    }

    ~Allocator() noexcept { deallocateBlocks(); }

    auto reset() -> void {
      deallocateBlocks();
      blocks.clear();
      next = 0;
    }

    template <typename... Ts>
    auto emplace(Ts&&... args) -> T* {
      if (next == 0) blocks.push_back(alloc.allocate(blockSize));
      auto const res = blocks.back() + next;
      std::construct_at(res, std::forward<Ts>(args)...);
      next++;
      if (next >= blockSize) next = 0;
      return res;
    }

    auto add(T const& obj) -> T* { return emplace(obj); }

    auto size() const -> size_t {
      if (next == 0) return blockSize * blocks.size();
      return blockSize * (blocks.size() - 1) + next;
    }

  private:
    size_t blockSize;
    std::allocator<T> alloc;
    std::vector<T*> blocks;
    size_t next;

    auto deallocateBlocks() -> void {
      for (auto i = 0uz; i < blocks.size(); i++) {
        std::destroy_n(blocks[i], (i + 1 == blocks.size() && next > 0) ? next : blockSize);
        alloc.deallocate(blocks[i], blockSize);
      }
    }
  };

}

#endif // BASE_HPP_
