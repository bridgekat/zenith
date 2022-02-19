// Server :: JSONRPC2Connection

#ifndef JSONRPC_HPP_
#define JSONRPC_HPP_

#include <iostream>
#include <thread>
#include <mutex>
#include <string>
#include <unordered_map>
#include <functional>
#include <future>
#include <nlohmann/json.hpp>


namespace Server {

  using std::string;
  using std::unordered_map;
  using nlohmann::json;

  class JSONRPC2Connection {
  public:
    enum ErrorCode: int {
      PARSE_ERROR      = -32700,
      INVALID_REQUEST  = -32600,
      METHOD_NOT_FOUND = -32601,
      INVALID_PARAMS   = -32602,
      INTERNAL_ERROR   = -32603,
      SERVER_ERROR     = -32099 // -32099 ~ -32000, reserved for implementation-defined
    };

    std::basic_istream<char>& in;
    std::basic_ostream<char>& out;
    std::jthread inThread;
    std::mutex outLock;

    unordered_map<string, std::function<void(JSONRPC2Connection*, int, const json&)>> methods;
    unordered_map<string, std::function<void(JSONRPC2Connection*, const json&)>> notifications;
    int nextid;
    unordered_map<int, std::promise<json>> promises;

    std::basic_ostream<char>& log;
    std::mutex logLock;

    JSONRPC2Connection(std::basic_istream<char>& in, std::basic_ostream<char>& out, std::basic_ostream<char>& log):
      in(in), out(out), inThread(), outLock(), methods(), notifications(), nextid(0), promises(), log(log), logLock() {}

    // While `inThread` is running, other threads should not read from the `in` stream.
    void startListen();
    void requestStop() { inThread.request_stop(); }
    void waitForComplete() { inThread.join(); }
    void handleRequest(const json& j);
    void send(const json& j);

    // Functions for sending requests.
    void callNotification(const string& method, const json& params) { send({{ "jsonrpc", "2.0" }, { "method", method }, { "params", params }}); }
    std::future<json> callMethod(const string& method, const json& params);

    // Functions for sending responses.
    void sendResult(int id, const json& result) { send({{ "jsonrpc", "2.0" }, { "id", id }, { "result", result }}); }
    // Only PARSE_ERROR or INVALID_REQUEST can have null id.
    template <ErrorCode C, typename std::enable_if_t<C == PARSE_ERROR || C == INVALID_REQUEST>* = nullptr>
    void sendError(const string& msg) { send({{ "jsonrpc", "2.0" }, { "id", nullptr }, { "error", {{ "code", C }, { "message", msg }}}}); }
    // Every condition except PARSE_ERROR and INVALID_REQUEST can have id.
    template <ErrorCode C, typename std::enable_if_t<C != PARSE_ERROR && C != INVALID_REQUEST>* = nullptr>
    void sendError(int id, const string& msg) { send({{ "jsonrpc", "2.0" }, { "id", id }, { "error", {{ "code", C }, { "message", msg }}}}); }
  };

}

#endif // JSONRPC_HPP_
