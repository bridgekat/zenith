// Server :: Coroutine

#ifndef COROUTINE_HPP_
#define COROUTINE_HPP_

#include <optional>
#include <memory>
#include <coroutine>
#include <exception>


namespace Server {

  using std::optional, std::nullopt;
  using std::shared_ptr;


  // DEBUG CODE
  extern int64_t DebugCounter;

  // Awaitable (chained) coroutines, for single-thread use only
  // See: https://en.cppreference.com/w/cpp/language/coroutines
  // See: https://www.scs.stanford.edu/~dm/blog/c++-coroutines.html
  // See: https://stackoverflow.com/questions/67930087/how-to-do-chained-coroutines-in-c-20
  // (This is so confusing, you should NOT try to understand it)
  // In the comments below, `A` refers to the caller/resumer coroutine, and `B` is a coroutine `co_await`ed by `A`.

  // The "coroutine future type".
  template <typename T = void>
  class Coroutine {
  public:
    // The "coroutine promise type".
    // See: https://stackoverflow.com/questions/68167497/c20-coroutines-why-is-the-promise-type-seperated-from-the-coroutine-object
    class promise_type {
    public:
      // Shared location for storing the result.
      // The promise associated with B is destroyed when B completes
      // (since B is started immediately on creation, this could happen before A tries to suspend),
      // so we cannot simply use `optional<T>` here.
      shared_ptr<optional<T>> result;
      // Shared location for storing any exceptions thrown.
      shared_ptr<std::exception_ptr> exptr;
      // If this is not null, it is resumed on `return_value(...)`.
      std::coroutine_handle<> then;

      promise_type(): result(new optional<T>()), exptr(new std::exception_ptr()), then() { DebugCounter++; }
      // DEBUG CODE
      promise_type(const promise_type& r): result(r.result), exptr(r.exptr), then(r.then) { DebugCounter++; }
      promise_type& operator=(const promise_type&) = default;
      ~promise_type() { DebugCounter--; }
      // DEBUG CODE END

      // Get future from promise
      Coroutine get_return_object() {
        // Obtaining an object (of type `std::coroutine_handle`) from one of its members (of type `promise_type`) is compiler magic!
        // See: https://stackoverflow.com/questions/58632651/how-coroutine-handlepromisefrom-promise-works-in-c
        return Coroutine(result, exptr, std::coroutine_handle<promise_type>::from_promise(*this));
      }

      // B is not suspended upon creation/completion
      std::suspend_never initial_suspend() noexcept { return {}; }
      std::suspend_never final_suspend() noexcept { return {}; }

      // B returns value (B.result := result, resume B.then (= continuation of A) if present)
      void return_value(const T& result) {
        *(this->result) = result;
        if (then) then.resume();
      }

      // B throws unhandled exception (B.exptr := exception, resume B.then (= continuation of A) if present)
      void unhandled_exception() {
        *exptr = std::current_exception();
        if (then) then.resume();
        else std::terminate();
      }
    };

    // `Coroutine` objects are not copyable but movable
    Coroutine(Coroutine&& r) = default;
    Coroutine& operator=(Coroutine&& r) = default;
    ~Coroutine() = default;

    // A is suspended if B didn't complete
    bool await_ready() const noexcept { return bool(*result); }
    // B didn't complete, store the continuation of A (B.then := continuation of A)
    void await_suspend(std::coroutine_handle<> ka) { handle.promise().then = ka; }
    // B completed or A was resumed, retrieve result (gives B.result to the continuation of A).
    // Either *(B.result) or *(B.exptr) must be available at this time,
    // as A must be resumed from either `B.return_value()` or `B.unhandled_exception()`.
    T&& await_resume() {
      if (*exptr) std::rethrow_exception(*exptr);
      return std::move(result->value());
    }

  private:
    // Invariant: pointers `result` and `exptr` must be valid.
    shared_ptr<optional<T>> result;
    shared_ptr<std::exception_ptr> exptr;
    std::coroutine_handle<promise_type> handle;

    // `Coroutine` objects must be constructed from `get_return_object()`!
    Coroutine(shared_ptr<optional<T>> result, shared_ptr<std::exception_ptr> exptr,
              std::coroutine_handle<promise_type>&& handle):
      result(result), exptr(exptr), handle(handle) {}
  };

  // We have to write these all over again, as using templates to select between
  // `return_value(...)` and `return_void()` doesn't work here (and there may be other complications).
  // See: https://devblogs.microsoft.com/oldnewthing/20210330-00/?p=105019
  template <>
  class Coroutine<void> {
  public:

    class promise_type {
    public:
      shared_ptr<bool> completed;
      shared_ptr<std::exception_ptr> exptr;
      std::coroutine_handle<> then;

      promise_type(): completed(new bool(false)), exptr(new std::exception_ptr()), then() { DebugCounter++; }
      // DEBUG CODE
      promise_type(const promise_type& r): completed(r.completed), exptr(r.exptr), then(r.then) { DebugCounter++; }
      promise_type& operator=(const promise_type&) = default;
      ~promise_type() { DebugCounter--; }
      // DEBUG CODE END

      Coroutine get_return_object() {
        return Coroutine(completed, exptr, std::coroutine_handle<promise_type>::from_promise(*this));
      }

      std::suspend_never initial_suspend() noexcept { return {}; }
      std::suspend_never final_suspend() noexcept { return {}; }

      void return_void() {
        *completed = true;
        if (then) then.resume();
      }

      void unhandled_exception() {
        *exptr = std::current_exception();
        if (then) then.resume();
        else std::terminate();
      }
    };

    Coroutine(Coroutine&& r) = default;
    Coroutine& operator=(Coroutine&& r) = default;
    ~Coroutine() = default;

    bool await_ready() const noexcept { return *completed; }
    void await_suspend(std::coroutine_handle<> ka) { handle.promise().then = ka; }
    void await_resume() const { if (*exptr) std::rethrow_exception(*exptr); }

  private:
    shared_ptr<bool> completed;
    shared_ptr<std::exception_ptr> exptr;
    std::coroutine_handle<promise_type> handle;

    Coroutine(shared_ptr<bool> completed, shared_ptr<std::exception_ptr> exptr,
              std::coroutine_handle<promise_type>&& handle):
      completed(completed), exptr(exptr), handle(handle) {}
  };

}

#endif // COROUTINE_HPP_
