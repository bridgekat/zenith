// Server :: JSONRPC2Exception, JSONRPC2Server

#ifndef JSONRPC2_HPP_
#define JSONRPC2_HPP_

#include <iostream>
#include <thread>
#include <mutex>
#include <utility>
#include <string>
#include <unordered_map>
#include <functional>
#include <stdexcept>
#include <nlohmann/json.hpp>
#include <core/base.hpp>
#include "coroutine.hpp"


namespace Server {

  using std::pair, std::string;
  using std::unordered_map;
  using nlohmann::json;


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
    // Use `json j = co_await srv->callMethod(...)` in a coroutine to send request and suspend
    // until a corresponding response is received.
    struct RequestAwaiter {
      JSONRPC2Server* srv;
      int64_t id;
      // Always suspend
      constexpr bool await_ready() const noexcept { return false; }
      // Store continuation at suspension
      void await_suspend(std::coroutine_handle<> k) { srv->ks[id] = { k, {} }; }
      // Retrieve result when resumed
      json&& await_resume() { return std::move(srv->ks[id].second); }
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

    // Active outgoing requests
    int64_t nextid;
    unordered_map<int, pair<std::coroutine_handle<void>, json>> ks;

    std::basic_ostream<char>& log;
    std::mutex logLock;

    std::optional<string> readNextPacket();
    void handleRequest(const json& j);

    // Functions for sending responses (should be thread-safe).
    void send(const json& j);
    void sendResult(int64_t id, const json& result) { send({{ "jsonrpc", "2.0" }, { "id", id }, { "result", result }}); }
    // Only PARSE_ERROR or INVALID_REQUEST can have null id.
    template <ErrorCode C, typename std::enable_if_t<C == PARSE_ERROR || C == INVALID_REQUEST>* = nullptr>
    void sendError(const string& msg) { send({{"jsonrpc", "2.0"}, {"id", nullptr}, {"error", {{"code", static_cast<int>(C)}, {"message", msg}}}}); }
    // Every condition except PARSE_ERROR and INVALID_REQUEST can have id.
    template <ErrorCode C, typename std::enable_if_t<C != PARSE_ERROR && C != INVALID_REQUEST>* = nullptr>
    void sendError(int64_t id, const string& msg) { send({{"jsonrpc", "2.0"}, {"id", id}, {"error", {{"code", static_cast<int>(C)}, {"message", msg}}}}); }
  };

}

#endif // JSONRPC2_HPP_
