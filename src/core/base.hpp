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

// Make sure to put these in the global scope.
using std::size_t;
using std::int8_t;
using std::int16_t;
using std::int32_t;
using std::int64_t;
using std::uint8_t;
using std::uint16_t;
using std::uint32_t;
using std::uint64_t;

// See: https://stackoverflow.com/questions/22346369/initialize-integer-literal-to-stdsize-t
constexpr auto operator"" _z(unsigned long long n) -> size_t { return n; }

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
    static constexpr auto DefaultBlockSize = 1024_z;

    Allocator(std::size_t blockSize = DefaultBlockSize):
      blockSize(blockSize),
      alloc(),
      blocks(),
      next(0) {}

    Allocator(Allocator&& r):
      blockSize(r.blockSize),
      alloc(r.alloc),
      blocks(std::move(r.blocks)),
      next(r.next) {}

    Allocator& operator=(Allocator&& r) noexcept {
      swap(*this, r);
      return *this;
    }

    friend void swap(Allocator& l, Allocator& r) noexcept {
      using std::swap;
      swap(l.blockSize, r.blockSize);
      swap(l.alloc, r.alloc);
      swap(l.blocks, r.blocks);
      swap(l.next, r.next);
    }

    ~Allocator() noexcept { deallocateBlocks(); }

    // TODO: add option to preserve allocated space
    void clear() {
      deallocateBlocks();
      blocks.clear();
      next = 0;
    }

    template <typename... Ts>
    T* emplaceBack(Ts&&... args) {
      if (next == 0) blocks.push_back(alloc.allocate(blockSize));
      T* res = blocks.back() + next;
      std::construct_at(res, std::forward<Ts>(args)...);
      next++;
      if (next >= blockSize) next = 0;
      return res;
    }

    T* pushBack(T const& obj) { return emplaceBack(obj); }

    std::size_t size() const {
      if (next == 0) return blockSize * blocks.size();
      return blockSize * (blocks.size() - 1) + next;
    }

  private:
    std::size_t blockSize;
    std::allocator<T> alloc;
    std::vector<T*> blocks;
    std::size_t next;

    void deallocateBlocks() {
      for (std::size_t i = 0; i < blocks.size(); i++) {
        std::destroy_n(blocks[i], (i + 1 == blocks.size() && next > 0) ? next : blockSize);
        alloc.deallocate(blocks[i], blockSize);
      }
    }
  };

}

#endif // BASE_HPP_
