// Server :: JSONRPC2Server

#ifndef JSONRPC2_HPP_
#define JSONRPC2_HPP_

#include <iostream>
#include <thread>
#include <mutex>
#include <utility>
#include <string>
#include <optional>
#include <memory>
#include <unordered_map>
#include <functional>
#include <coroutine>
#include <type_traits>
#include <stdexcept>
#include <nlohmann/json.hpp>
#include <core/base.hpp>


namespace Server {

  using std::pair, std::string;
  using std::optional, std::nullopt, std::shared_ptr;
  using std::unordered_map;
  using nlohmann::json;


  extern int64_t debugCounter;

  // Awaitable (chained) coroutines
  // See: https://en.cppreference.com/w/cpp/language/coroutines
  // See: https://www.scs.stanford.edu/~dm/blog/c++-coroutines.html
  // See: https://stackoverflow.com/questions/67930087/how-to-do-chained-coroutines-in-c-20
  // (This is so confusing, you should NOT try to understand it)
  // In the comments below, `A` refers to the caller/resumer coroutine, and `B` is a coroutine `co_await`ed by `A`.
  template <typename T = void>
  struct Coroutine {

    // See: https://stackoverflow.com/questions/68167497/c20-coroutines-why-is-the-promise-type-seperated-from-the-coroutine-object
    struct promise_type {
      shared_ptr<optional<T>> result; // Shared location for storing the result.
      std::coroutine_handle<> then;   // If this is not null, it is resumed on `return`.

      promise_type(): result(new optional<T>()), then() { debugCounter++; }
      promise_type(const promise_type& r): result(r.result), then(r.then) { debugCounter++; }
      promise_type& operator=(const promise_type&) = default;
      ~promise_type() { debugCounter--; }

      // Obtaining an object (of type `std::coroutine_handle`) from one of its members (of type `promise_type`) is compiler magic!
      // See: https://stackoverflow.com/questions/58632651/how-coroutine-handlepromisefrom-promise-works-in-c
      Coroutine<T> get_return_object() {
        return Coroutine<T>{ result, std::coroutine_handle<promise_type>::from_promise(*this) };
      }

      // B is not suspended upon creation/completion
      std::suspend_never initial_suspend() noexcept { return {}; }
      std::suspend_never final_suspend() noexcept { return {}; }

      // B returns value (B.promise.result := result, resume B.promise.then == continuation of A if present)
      void return_value(const T& result) {
        std::cerr << "Returned" << std::endl;
        *(this->result) = result;
        if (then) then.resume();
      }

      // B throws unhandled exception (TODO)
      void unhandled_exception() {}
    };

    // Invariant: `result` must be valid. (`Coroutine` objects must be constructed from `get_return_object()`!)
    shared_ptr<optional<T>> result;
    std::coroutine_handle<promise_type> handle;

    // A is always suspended
    bool await_ready() const noexcept { std::cerr << "Queried: " << bool(*result) << std::endl; return bool(*result); }
    // Stores the continuation of A upon suspension of A (B.promise.then := continuation of A)
    void await_suspend(std::coroutine_handle<> ka) { std::cerr << "Suspended" << std::endl; handle.promise().then = ka; }
    // Retrieve result when resumed (gives B.promise.result to the continuation of A)
    // (Invariant: *(B.result) must be available at this time.)
    T&& await_resume() { std::cerr << "Resumed" << std::endl; return std::move(result->value()); }
  };

  // We have to write these all over again, as using templates to select between
  // `return_value(...)` and `return_void()` doesn't work here (and there may be other complications).
  // See: https://devblogs.microsoft.com/oldnewthing/20210330-00/?p=105019
  template <>
  struct Coroutine<void> {

    struct promise_type {
      shared_ptr<bool> completed;   // Shared location for storing the result.
      std::coroutine_handle<> then; // If this is not null, it is resumed on `return`.

      promise_type(): completed(new bool), then() { debugCounter++; }
      promise_type(const promise_type& r): completed(r.completed), then(r.then) { debugCounter++; }
      promise_type& operator=(const promise_type&) = default;
      ~promise_type() { debugCounter--; }

      Coroutine<void> get_return_object() {
        return Coroutine<void>{ completed, std::coroutine_handle<promise_type>::from_promise(*this) };
      }

      std::suspend_never initial_suspend() noexcept { return {}; }
      std::suspend_never final_suspend() noexcept { return {}; }

      // B completes (resume B.promise.then == continuation of A if present)
      void return_void() { *completed = true; if (then) then.resume(); }

      // B throws unhandled exception (TODO)
      void unhandled_exception() {}
    };

    // Invariant: `completed` must be valid. (`Coroutine` objects must be constructed from `get_return_object()`!)
    shared_ptr<bool> completed;
    std::coroutine_handle<promise_type> handle;

    bool await_ready() const noexcept { return *completed; }
    void await_suspend(std::coroutine_handle<> ka) { handle.promise().then = ka; }
    constexpr void await_resume() const noexcept {}
  };

  // The following implementation is written against LSP 3.16 and JSON-RPC 2.0
  // See: https://microsoft.github.io/language-server-protocol/specifications/specification-current/#headerPart
  // See: https://www.jsonrpc.org/specification

  struct JSONRPC2Exception: public std::runtime_error {
    enum class ErrorCode: short {
      PARSE_ERROR      = -32700,
      INVALID_REQUEST  = -32600,
      METHOD_NOT_FOUND = -32601,
      INVALID_PARAMS   = -32602,
      INTERNAL_ERROR   = -32603,
      SERVER_ERROR     = -32099 // -32099 ~ -32000, reserved for implementation-defined
    };
    ErrorCode code;
    explicit JSONRPC2Exception(ErrorCode code, const string& s = ""):
      std::runtime_error(s), code(code) {}
  };

  using ErrorCode = JSONRPC2Exception::ErrorCode;
  using enum ErrorCode;

  class JSONRPC2Server {
  public:
    // Use `json j = co_await srv->callMethod(...)` in a Coroutine to send request and suspend
    // until a corresponding response is received.
    struct RequestAwaiter {
      JSONRPC2Server* srv;
      int64_t id;
      // Always suspend
      constexpr bool await_ready() const noexcept { return false; }
      // Store continuation at suspension
      void await_suspend(std::coroutine_handle<void> h) const { srv->ks[id] = { h, {} }; }
      // Retrieve result when resumed
      // json await_resume() const { return srv->ks[id].second; }
      // Due to a limitation in GCC, await_resume() cannot return complex objects:
      // See: https://stackoverflow.com/questions/67860049/why-cant-co-await-return-a-string
      int64_t await_resume() const { return id; }
    };

    // While `inThread` is running, other threads should not read from the `in` stream.
    JSONRPC2Server(std::basic_istream<char>& in, std::basic_ostream<char>& out, std::basic_ostream<char>& log):
      in(in), inThread(), out(out), outLock(), methods(), notifications(), nextid(0), ks(), log(log), logLock() {}

    // These functions should only be called when `inThread` is not running.
    // See: https://stackoverflow.com/questions/33943601/check-if-stdthread-is-still-running
    // See: https://stackoverflow.com/questions/18365532/should-i-pass-an-stdfunction-by-const-reference
    void addMethod(const string& name, std::function<Coroutine<json>(JSONRPC2Server*, json)> f) {
      if (inThread.joinable()) throw Core::NotImplemented();
      methods.emplace(name, f);
    }
    void addNotification(const string& name, std::function<Coroutine<void>(JSONRPC2Server*, json)> f) {
      if (inThread.joinable()) throw Core::NotImplemented();
      notifications.emplace(name, f);
    }

    // Functions for sending requests (should be thread-safe).
    void callNotification(const string& method, const json& params) { send({{"jsonrpc", "2.0"}, {"method", method}, {"params", params}}); }
    RequestAwaiter callMethod(const string& method, const json& params);

    // Functions for sending responses (should be thread-safe).
    void sendResult(int64_t id, const json& result) { send({{"jsonrpc", "2.0"}, {"id", id}, {"result", result}}); }
    // Only PARSE_ERROR or INVALID_REQUEST can have null id.
    template <ErrorCode C, typename std::enable_if_t<C == PARSE_ERROR || C == INVALID_REQUEST>* = nullptr>
    void sendError(const string& msg) { send({{"jsonrpc", "2.0"}, {"id", nullptr}, {"error", {{"code", static_cast<int>(C)}, {"message", msg}}}}); }
    // Every condition except PARSE_ERROR and INVALID_REQUEST can have id.
    template <ErrorCode C, typename std::enable_if_t<C != PARSE_ERROR && C != INVALID_REQUEST>* = nullptr>
    void sendError(int64_t id, const string& msg) { send({{"jsonrpc", "2.0"}, {"id", id}, {"error", {{"code", static_cast<int>(C)}, {"message", msg}}}}); }

    void startListen();
    void requestStop() { inThread.request_stop(); }
    void waitForComplete() { inThread.join(); }
    size_t numActiveCoroutines() const { return ks.size(); }

    // Due to a limitation in GCC, await_resume() cannot return complex objects, so we temporarily use this function to retrieve results...
    const json& getResult(int64_t id) { return ks[id].second; }

  private:
    std::basic_istream<char>& in;
    std::jthread inThread;
    std::basic_ostream<char>& out;
    std::mutex outLock;

    unordered_map<string, std::function<Coroutine<json>(JSONRPC2Server*, json)>> methods;
    unordered_map<string, std::function<Coroutine<void>(JSONRPC2Server*, json)>> notifications;

    // Active coroutines (continuations)
    int64_t nextid;
    unordered_map<int, pair<std::coroutine_handle<void>, json>> ks;

    std::basic_ostream<char>& log;
    std::mutex logLock;

    void handleRequest(const json& j);
    void send(const json& j);
  };

}

#endif // JSONRPC2_HPP_
