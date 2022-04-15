// Core :: Allocator, Unreachable, NotImplemented, NonExhaustive

#ifndef BASE_HPP_
#define BASE_HPP_

#include <vector>
#include <memory>
#include <utility>
#include <string>
#include <stdexcept>


namespace Core {

  // A simple region-based memory allocator: https://news.ycombinator.com/item?id=26433654
  // This ensures that objects stay in the same place
  template <typename T>
  class Allocator {
  public:
    Allocator(std::size_t blockSize = 1024):
      blockSize(blockSize),
      alloc(),
      blocks(),
      next(0) {}

    Allocator(Allocator&& r) noexcept:
      blockSize(r.blockSize),
      alloc(std::move(r.alloc)),
      blocks(std::move(r.blocks)), // Guarantees to leave r.blocks empty
      next(std::exchange(r.next, 0)) {}

    Allocator& operator=(Allocator&& r) noexcept {
      if (this != &r) {
        deallocateBlocks();
        blockSize = r.blockSize;
        alloc = std::move(r.alloc);
        blocks = std::move(r.blocks);
        next = std::exchange(r.next, 0);
      }
      return *this;
    }

    ~Allocator() {
      deallocateBlocks();
    }

    // TODO: preserve allocated space?
    void clear() noexcept {
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

    T* pushBack(const T& obj) {
      return emplaceBack(obj);
    }

    std::size_t size() const noexcept {
      if (next == 0) return blockSize * blocks.size();
      return blockSize * (blocks.size() - 1) + next;
    }

  private:
    std::size_t blockSize;
    std::allocator<T> alloc;
    std::vector<T*> blocks;
    std::size_t next;

    void deallocateBlocks() noexcept {
      for (size_t i = 0; i < blocks.size(); i++) {
        std::destroy_n(blocks[i], (i + 1 == blocks.size() && next > 0)? next : blockSize);
        alloc.deallocate(blocks[i], blockSize);
      }
    }
  };

  // Some exception classes...
  struct Unreachable: public std::logic_error {
    explicit Unreachable(const std::string& s = ""):
      std::logic_error("\"Unreachable\" code was reached" + (s.empty() ? "" : ": " + s)) {}
  };
  struct NotImplemented: public std::logic_error {
    explicit NotImplemented(const std::string& s = ""):
      std::logic_error("\"Not implemented\" code was called" + (s.empty() ? "" : ": " + s)) {}
  };
  struct NonExhaustive: public Unreachable {
    NonExhaustive(): Unreachable("unknown tagged union state") {}
  };

}

#endif // BASE_HPP_
