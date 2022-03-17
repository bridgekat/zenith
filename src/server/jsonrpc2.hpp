// Server :: JSONRPC2Exception, JSONRPC2Server

#ifndef JSONRPC2_HPP_
#define JSONRPC2_HPP_

#include <iostream>
#include <thread>
#include <string>
#include <unordered_map>
#include <functional>
#include <stdexcept>
#include <nlohmann/json.hpp>
#include <core/base.hpp>
#include "coroutine.hpp"


namespace Server {

  using std::string;
  using std::unordered_map;
  using nlohmann::json;


  // The following implementation is written against LSP 3.16 and JSON-RPC 2.0
  // See: https://microsoft.github.io/language-server-protocol/specifications/specification-current/#headerPart
  // See: https://www.jsonrpc.org/specification

  struct JSONRPC2Exception: public std::runtime_error {
    enum ErrorCode: int {
      PARSE_ERROR            = -32700,
      INVALID_REQUEST        = -32600,
      METHOD_NOT_FOUND       = -32601,
      INVALID_PARAMS         = -32602,
      INTERNAL_ERROR         = -32603,
      // LSP-specific error codes
      SERVER_NOT_INITIALIZED = -32002,
      UNKNOWN_ERROR_CODE     = -32001,
      CONTENT_MODIFIED       = -32801,
      REQUEST_CANCELLED      = -32800
    };
    ErrorCode code;
    explicit JSONRPC2Exception(ErrorCode code, const string& s = ""):
      std::runtime_error(s), code(code) {}
  };
  using ErrorCode = JSONRPC2Exception::ErrorCode;
  using enum ErrorCode;

  class JSONRPC2Server {
  public:
    struct RequestAwaiter;

    // While `inThread` is running, other threads should not read/write the `in`/`out`/`log` streams...
    JSONRPC2Server(std::basic_istream<char>& in, std::basic_ostream<char>& out, std::basic_ostream<char>& log):
      in(in), out(out), log(log), inThread(), methods(), notifications(), nextid(0), requests() {}

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

    // Functions for sending requests (should only be called from `inThread`).
    void callNotification(const string& method, const json& params);
    RequestAwaiter callMethod(const string& method, const json& params);

    // Represents an active outgoing request.
    struct RequestEntry {
      std::coroutine_handle<void> k;
      std::exception_ptr exptr;
      json result;

      RequestEntry(std::coroutine_handle<void> k = std::coroutine_handle<void>()):
        k(k), exptr(nullptr), result({}) {}
    };

    size_t numActiveRequests() const { return requests.size(); }

    // Use `json j = co_await srv->callMethod(...)` in a coroutine to send request and suspend
    // until a corresponding response is received (should only be used from `inThread`).
    struct RequestAwaiter {
      JSONRPC2Server* srv;
      int64_t id;
      // Always suspend
      constexpr bool await_ready() const noexcept { return false; }
      // Store continuation at suspension
      void await_suspend(std::coroutine_handle<> k) const { srv->requests.emplace(id, k); }
      // Retrieve result when resumed
      // Pre: requests[id] must be present
      json&& await_resume() const {
        RequestEntry& req = srv->requests[id];
        if (req.exptr) std::rethrow_exception(req.exptr);
        return std::move(req.result);
      }
    };

    void startListen();
    void requestStop() { inThread.request_stop(); }
    void waitForComplete() { inThread.join(); }

  private:
    std::basic_istream<char>& in;
    std::basic_ostream<char>& out;
    std::basic_ostream<char>& log;
    std::jthread inThread;

    unordered_map<string, std::function<Coroutine<json>(JSONRPC2Server*, json)>> methods;
    unordered_map<string, std::function<Coroutine<void>(JSONRPC2Server*, json)>> notifications;

    // Active outgoing requests
    int64_t nextid;
    unordered_map<int64_t, RequestEntry> requests;

    std::optional<string> readNextPacket();
    void handleRequest(const json& j);

    // Functions for sending responses (should only be called from `inThread`).
    void send(const json& j);
    void sendResult(int64_t id, const json& result);
    void sendError(ErrorCode code, const string& msg);
    void sendError(int64_t id, ErrorCode code, const string& msg);
  };

}

#endif // JSONRPC2_HPP_
