#ifndef BASE_HPP_
#define BASE_HPP_

#include <vector>
#include <string>
#include <stdexcept>


namespace Core {

  // A simple region-based memory allocator: https://news.ycombinator.com/item?id=26433654
  // This ensures that objects stay in the same place
  template <typename T>
  class Allocator {
  private:
    size_t bSize, next;
    std::vector<T*> blocks;

  public:
    Allocator(size_t blockSize = 1024): bSize(blockSize), next(0), blocks() {}
    Allocator(Allocator&&) = default;
    Allocator& operator=(Allocator&&) = default;
    ~Allocator() { for (auto p: blocks) delete[] p; }

    T* pushBack(const T& obj) {
      if (next == 0) blocks.push_back(new T[bSize]);
      T* res = &blocks.back()[next];
      *res = obj;
      next++; if (next >= bSize) next = 0;
      return res;
    }

    size_t size() const {
      if (next == 0) return bSize * blocks.size();
      return bSize * (blocks.size() - 1) + next;
    }
  };

  // Some exception classes...
  struct Unreachable: public std::logic_error { Unreachable(): std::logic_error("\"Unreachable\" code was reached") {} };
  struct CheckFailure: public std::logic_error { CheckFailure(const std::string& s): std::logic_error(s) {} };

}

#endif // BASE_HPP_