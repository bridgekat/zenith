#ifndef APIMU_SERVER_COROUTINE_HPP
#define APIMU_SERVER_COROUTINE_HPP

#include <coroutine>
#include <exception>
#include <memory>
#include <optional>
#include <utility>

namespace apimu::server {

  // Awaitable (chained) coroutines, for single-thread use only.
  // Not an optimal implementation, but should be enough for current purpose...
  // See: https://en.cppreference.com/w/cpp/language/coroutines
  // See: https://www.scs.stanford.edu/~dm/blog/c++-coroutines.html
  // See: https://stackoverflow.com/questions/67930087/how-to-do-chained-coroutines-in-c-20
  // In the comments below, `A` refers to the caller/resumer coroutine, and `B` is a coroutine `co_await`ed by `A`.

  // The "coroutine future type".
  template <typename T>
  class Coroutine {
  public:
    // The "coroutine promise type".
    // See:
    // https://stackoverflow.com/questions/68167497/c20-coroutines-why-is-the-promise-type-seperated-from-the-coroutine-object
    class promise_type {
    public:
      // Shared location for storing the result.
      // The promise associated with B is destroyed when B completes (since B is started immediately on creation, this
      // could happen before A tries to suspend), so we cannot simply use `optional<T>` here.
      std::shared_ptr<std::optional<T>> result{new std::optional<T>()};

      // Shared location for storing any exceptions thrown.
      std::shared_ptr<std::exception_ptr> exptr{new std::exception_ptr()};

      // If this is not null, it is resumed on `return_value(...)`.
      std::coroutine_handle<> then;

      // Get future from promise
      auto get_return_object() -> Coroutine {
        // Obtaining an object (of type `std::coroutine_handle`) from one of its members (of type `promise_type`) is
        // compiler magic! See:
        // https://stackoverflow.com/questions/58632651/how-coroutine-handlepromisefrom-promise-works-in-c
        return {result, exptr, std::coroutine_handle<promise_type>::from_promise(*this)};
      }

      // B is not suspended upon creation/completion
      auto initial_suspend() noexcept -> std::suspend_never { return {}; }
      auto final_suspend() noexcept -> std::suspend_never { return {}; }

      // B returns value (B.result := result, resume B.then (= continuation of A) if present)
      auto return_value(T const& result) -> void {
        *(this->result) = result;
        if (then) then.resume();
      }

      // B throws unhandled exception (B.exptr := exception, resume B.then (= continuation of A) if present)
      auto unhandled_exception() -> void {
        *exptr = std::current_exception();
        if (then) then.resume();
      }
    };

    // `Coroutine` objects are not copyable but movable
    Coroutine(Coroutine const&) = delete;
    Coroutine(Coroutine&&) = default;
    auto operator=(Coroutine const&) -> Coroutine& = delete;
    auto operator=(Coroutine&&) -> Coroutine& = default;
    ~Coroutine() = default;

    // A is suspended if B didn't complete
    auto await_ready() const -> bool {
      if (*exptr) std::rethrow_exception(*exptr);
      return (*result).has_value();
    }

    // B didn't complete, store the continuation of A (B.then := continuation of A)
    auto await_suspend(std::coroutine_handle<> ka) -> void { handle.promise().then = ka; }

    // B completed or A was resumed, retrieve result (gives B.result to the continuation of A).
    // Either *(B.result) or *(B.exptr) must be available at this time, as A must be resumed from either
    // `B.return_value()` or `B.unhandled_exception()`.
    auto await_resume() -> T {
      if (*exptr) std::rethrow_exception(*exptr);
      return std::move(result->value());
    }

  private:
    // Invariant: pointers `result` and `exptr` must be valid.
    std::shared_ptr<std::optional<T>> result;
    std::shared_ptr<std::exception_ptr> exptr;
    std::coroutine_handle<promise_type> handle;

    // `Coroutine` objects must be constructed from `get_return_object()`!
    Coroutine(
      std::shared_ptr<std::optional<T>> result,
      std::shared_ptr<std::exception_ptr> exptr,
      std::coroutine_handle<promise_type> handle
    ):
      result(std::move(result)),
      exptr(std::move(exptr)),
      handle(handle) {}
  };

  // We have to write these all over again, as using templates to select between
  // `return_value(...)` and `return_void()` doesn't work here (and there may be other complications).
  // See: https://devblogs.microsoft.com/oldnewthing/20210330-00/?p=105019
  template <>
  class Coroutine<void> {
  public:
    class promise_type {
    public:
      std::shared_ptr<bool> completed{new bool(false)};
      std::shared_ptr<std::exception_ptr> exptr{new std::exception_ptr()};
      std::coroutine_handle<> then;

      auto get_return_object() -> Coroutine {
        return {completed, exptr, std::coroutine_handle<promise_type>::from_promise(*this)};
      }

      auto initial_suspend() noexcept -> std::suspend_never { return {}; }
      auto final_suspend() noexcept -> std::suspend_never { return {}; }

      auto return_void() -> void {
        *completed = true;
        if (then) then.resume();
      }

      auto unhandled_exception() -> void {
        *exptr = std::current_exception();
        if (then) then.resume();
      }
    };

    Coroutine(Coroutine const&) = delete;
    Coroutine(Coroutine&&) = default;
    auto operator=(Coroutine const&) -> Coroutine& = delete;
    auto operator=(Coroutine&&) -> Coroutine& = default;
    ~Coroutine() = default;

    auto await_ready() const -> bool {
      if (*exptr) std::rethrow_exception(*exptr);
      return *completed;
    }
    auto await_suspend(std::coroutine_handle<> ka) -> void { handle.promise().then = ka; }
    auto await_resume() const -> void {
      if (*exptr) std::rethrow_exception(*exptr);
    }

  private:
    std::shared_ptr<bool> completed;
    std::shared_ptr<std::exception_ptr> exptr;
    std::coroutine_handle<promise_type> handle;

    Coroutine(
      std::shared_ptr<bool> completed,
      std::shared_ptr<std::exception_ptr> exptr,
      std::coroutine_handle<promise_type>&& handle
    ):
      completed(std::move(completed)),
      exptr(std::move(exptr)),
      handle(handle) {}
  };

}

#endif // APIMU_SERVER_COROUTINE_HPP
