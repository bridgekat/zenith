// Server :: JSONRPC2Server

#ifndef JSONRPC_HPP_
#define JSONRPC_HPP_

#include <iostream>
#include <thread>
#include <mutex>
#include <utility>
#include <string>
#include <unordered_map>
#include <functional>
#include <coroutine>
#include <nlohmann/json.hpp>
#include <core/base.hpp>


namespace Server {

  using std::pair, std::string;
  using std::unordered_map;
  using nlohmann::json;


  class JSONRPC2Server {
  public:
    // Coroutines support
    // See: https://en.cppreference.com/w/cpp/language/coroutines
    // See: https://www.scs.stanford.edu/~dm/blog/c++-coroutines.html
    struct Coroutine {
      struct promise_type {
        Coroutine get_return_object() { return {}; }
        std::suspend_never initial_suspend() noexcept { return {}; }
        std::suspend_never final_suspend() noexcept { return {}; }
        void return_void() {}
        void unhandled_exception() {}
      };
    };

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

    // The following implementation is written against LSP 3.16 and JSON-RPC 2.0
    // See: https://microsoft.github.io/language-server-protocol/specifications/specification-current/#headerPart
    // See: https://www.jsonrpc.org/specification

    enum ErrorCode: short {
      PARSE_ERROR      = -32700,
      INVALID_REQUEST  = -32600,
      METHOD_NOT_FOUND = -32601,
      INVALID_PARAMS   = -32602,
      INTERNAL_ERROR   = -32603,
      SERVER_ERROR     = -32099 // -32099 ~ -32000, reserved for implementation-defined
    };

    // While `inThread` is running, other threads should not read from the `in` stream.
    JSONRPC2Server(std::basic_istream<char>& in, std::basic_ostream<char>& out, std::basic_ostream<char>& log):
      in(in), out(out), inThread(), outLock(), methods(), notifications(), nextid(0), ks(), log(log), logLock() {}

    // These functions should only be called when `inThread` is not running.
    // See: https://stackoverflow.com/questions/33943601/check-if-stdthread-is-still-running
    // See: https://stackoverflow.com/questions/18365532/should-i-pass-an-stdfunction-by-const-reference
    void addMethod(const string& name, std::function<Coroutine(JSONRPC2Server*, int, const json&)> f) {
      if (inThread.joinable()) throw Core::NotImplemented();
      methods.emplace(name, f);
    }
    void addNotification(const string& name, std::function<Coroutine(JSONRPC2Server*, const json&)> f) {
      if (inThread.joinable()) throw Core::NotImplemented();
      notifications.emplace(name, f);
    }

    // Functions for sending requests (should be thread-safe).
    void callNotification(const string& method, const json& params) { send({{ "jsonrpc", "2.0" }, { "method", method }, { "params", params }}); }
    RequestAwaiter callMethod(const string& method, const json& params);

    // Functions for sending responses (should be thread-safe).
    void sendResult(int64_t id, const json& result) { send({{ "jsonrpc", "2.0" }, { "id", id }, { "result", result }}); }
    // Only PARSE_ERROR or INVALID_REQUEST can have null id.
    template <ErrorCode C, typename std::enable_if_t<C == PARSE_ERROR || C == INVALID_REQUEST>* = nullptr>
    void sendError(const string& msg) { send({{ "jsonrpc", "2.0" }, { "id", nullptr }, { "error", {{ "code", C }, { "message", msg }}}}); }
    // Every condition except PARSE_ERROR and INVALID_REQUEST can have id.
    template <ErrorCode C, typename std::enable_if_t<C != PARSE_ERROR && C != INVALID_REQUEST>* = nullptr>
    void sendError(int64_t id, const string& msg) { send({{ "jsonrpc", "2.0" }, { "id", id }, { "error", {{ "code", C }, { "message", msg }}}}); }

    void startListen();
    void requestStop() { inThread.request_stop(); }
    void waitForComplete() { inThread.join(); }
    size_t numActiveCoroutines() const { return ks.size(); }

    // Due to a limitation in GCC, await_resume() cannot return complex objects, so we temporarily use this function to retrieve results...
    const json& getResult(int64_t id) { return ks[id].second; }

  private:
    std::basic_istream<char>& in;
    std::basic_ostream<char>& out;
    std::jthread inThread;
    std::mutex outLock;

    unordered_map<string, std::function<Coroutine(JSONRPC2Server*, int, const json&)>> methods;
    unordered_map<string, std::function<Coroutine(JSONRPC2Server*, const json&)>> notifications;

    // Active coroutines (continuations)
    int64_t nextid;
    unordered_map<int, pair<std::coroutine_handle<void>, json>> ks;

    std::basic_ostream<char>& log;
    std::mutex logLock;

    void handleRequest(const json& j);
    void send(const json& j);
  };

}

#endif // JSONRPC_HPP_
