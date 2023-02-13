#ifndef APIMU_SERVER_JSON_RPC_SERVER_HPP
#define APIMU_SERVER_JSON_RPC_SERVER_HPP

#include <functional>
#include <iosfwd>
#include <stdexcept>
#include <string>
#include <thread>
#include <unordered_map>
#include <common.hpp>
#include <nlohmann/json.hpp>
#include "coroutine.hpp"

namespace apimu::server {
#include "macros_open.hpp"

  // The following implementation is written against LSP 3.16 and JSON-RPC 2.0
  // See: https://microsoft.github.io/language-server-protocol/specifications/specification-current/#headerPart
  // See: https://www.jsonrpc.org/specification
  enum ErrorCode : int32_t {
    parseError = -32700,
    invalidRequest = -32600,
    methodNotFound = -32601,
    invalidParams = -32602,
    internalError = -32603,
    // LSP-specific error codes
    serverNotInitialized = -32002,
    unknown = -32001,
    contentModified = -32801,
    requestCancelled = -32800
  };

  struct JsonRpcException: std::runtime_error {
    ErrorCode code;
    explicit JsonRpcException(ErrorCode code, std::string const& s = ""):
      std::runtime_error(s),
      code(code) {}
  };

  class JsonRpcServer {
  public:
    struct RequestAwaitable;

    // While `inThread` is running, other threads should not read/write the `in`/`out`/`log` streams...
    JsonRpcServer(std::basic_istream<char>& in, std::basic_ostream<char>& out /*, std::basic_ostream<char>& log */):
      in(in),
      out(out)
    /* log(log), */
    {}

    // These functions should only be called when `inThread` is not running.
    // See: https://stackoverflow.com/questions/33943601/check-if-stdthread-is-still-running
    auto addMethod(std::string const& name, std::function<Coroutine<nlohmann::json>(JsonRpcServer*, nlohmann::json)> f)
      -> void {
      assert(!inThread.joinable());
      methods.emplace(name, std::move(f));
    }
    auto addNotification(std::string const& name, std::function<Coroutine<void>(JsonRpcServer*, nlohmann::json)> f)
      -> void {
      assert(!inThread.joinable());
      notifications.emplace(name, std::move(f));
    }

    // Functions for sending requests (should only be called from `inThread`).
    auto callNotification(std::string const& method, nlohmann::json const& params) -> void;
    auto callMethod(std::string const& method, nlohmann::json const& params) -> RequestAwaitable;

    // Represents an active outgoing request.
    struct RequestEntry {
      std::coroutine_handle<void> k;
      std::exception_ptr exptr = nullptr;
      nlohmann::json result = {};
      explicit RequestEntry(std::coroutine_handle<void> k = std::coroutine_handle<void>()):
        k(k) {}
    };

    auto numActiveRequests() const -> size_t { return requests.size(); }

    // Use `json j = co_await srv->callMethod(...)` in a coroutine to send request and suspend
    // until a corresponding response is received (should only be used from `inThread`).
    struct RequestAwaitable {
      JsonRpcServer* srv;
      std::int64_t id;
      // Always suspend
      auto await_ready() const noexcept -> bool { return false; }
      // Store continuation at suspension
      auto await_suspend(std::coroutine_handle<> k) const -> void { srv->requests.emplace(id, k); }
      // Retrieve result when resumed
      // Pre: requests[id] must be present
      auto await_resume() const -> nlohmann::json {
        auto& req = srv->requests[id];
        if (req.exptr) std::rethrow_exception(req.exptr);
        return std::move(req.result);
      }
    };

    auto startListen() -> void;
    auto requestStop() -> void { inThread.request_stop(); }
    auto waitForComplete() -> void { inThread.join(); }

  private:
    std::basic_istream<char>& in;
    std::basic_ostream<char>& out;
    // std::basic_ostream<char>& log;
    std::jthread inThread;

    std::unordered_map<std::string, std::function<Coroutine<nlohmann::json>(JsonRpcServer*, nlohmann::json)>> methods;
    std::unordered_map<std::string, std::function<Coroutine<void>(JsonRpcServer*, nlohmann::json)>> notifications;

    // Active outgoing requests
    int64_t nextid = 0;
    std::unordered_map<int64_t, RequestEntry> requests;

    auto readNextPacket() -> std::optional<std::string>;
    auto handleRequest(nlohmann::json const& j) -> void;

    // Functions for sending responses (should only be called from `inThread`).
    auto send(nlohmann::json const& j) -> void;
    auto sendResult(int64_t id, nlohmann::json const& result) -> void;
    auto sendError(ErrorCode code, std::string const& msg) -> void;
    auto sendError(int64_t id, ErrorCode code, std::string const& msg) -> void;
  };

#include "macros_close.hpp"
}

#endif // APIMU_SERVER_JSON_RPC_SERVER_HPP
