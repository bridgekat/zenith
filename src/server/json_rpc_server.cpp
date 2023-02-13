#include "json_rpc_server.hpp"
#include <iostream>
#include <optional>

namespace apimu::server {
#include "macros_open.hpp"

  auto JsonRpcServer::callNotification(std::string const& method, nlohmann::json const& params) -> void {
    send({
      {"jsonrpc",  "2.0"},
      { "method", method},
      { "params", params}
    });
  }

  auto JsonRpcServer::callMethod(std::string const& method, nlohmann::json const& params) -> RequestAwaitable {
    auto res = RequestAwaitable{this, nextid};
    send({
      {"jsonrpc",  "2.0"},
      {     "id", nextid},
      { "method", method},
      { "params", params}
    });
    nextid++;
    return res;
  }

  // The only supported value for Content-Type
  constexpr std::string_view contentType = "application/vscode-jsonrpc; charset=utf-8";

  // Returns `nullopt` if read past EOF.
  // For discussions on non-blocking `cin`, see:
  // https://stackoverflow.com/questions/16592357/non-blocking-stdgetline-exit-if-no-input The following code uses
  // blocking input, which is enough for the current purpose.
  auto JsonRpcServer::readNextPacket() -> std::optional<std::string> {
    // `std::getline()` and then trim trailing "\r\n"
    // ("\r\n" is used as EOL in LSP 3.16 header part)
    auto getline = [this]() {
      auto res = std::string();
      std::getline(in, res);
      if (!res.empty() && res.back() == '\r') res.pop_back();
      return res;
    };

    // Read header part
    auto n = 0_z;
    auto s = getline();

    while (s != "") {
      auto const p = s.find(": ");
      if (p == std::string::npos) unimplemented;
      auto const key = s.substr(0, p), value = s.substr(p + 2);
      // log << "<< \"" << key << "\" = \"" << value << "\"" << std::endl;

      if (key == "Content-Length") {
        auto ss = std::stringstream(value);
        ss >> n;
      } else if (key == "Content-Type") {
        if (value != contentType) unimplemented;
      } else {
        unimplemented;
      }

      // Get next line
      s = getline();
    }

    // End of header, get content
    s.resize(n);
    in.read(s.data(), static_cast<std::streamsize>(n));
    // log << "<< " << s << std::endl << std::endl;

    if (in.eof()) return {};
    return s;
  }

  auto JsonRpcServer::startListen() -> void {
    // Start the listener thread (`inThread`)
    // For an example of using `std::jthread`, see: https://en.cppreference.com/w/cpp/thread/stop_token
    inThread = std::jthread([this](std::stop_token stopToken) {
      // Main loop
      while (!stopToken.stop_requested()) {
        auto const o = readNextPacket();

        // Though LSP 3.16 says [1] that an Exit Notification after a Shutdown Request actually stops the server,
        // VSCode simply closes the input stream without giving an Exit Notification.
        // This line is used to stop the input listener thread in that case.
        //   [1]: https://microsoft.github.io/language-server-protocol/specifications/specification-3-16/#shutdown
        if (!o.has_value()) break;

        // Parse JSON-RPC 2.0 requests/notifications
        auto j = nlohmann::json();
        try {
          j = nlohmann::json::parse(*o);
        } catch (nlohmann::json::parse_error& e) {
          sendError(ErrorCode::parseError, e.what());
          continue;
        }

        // Handle JSON request
        if (j.is_object()) handleRequest(j);
        else if (j.is_array()) unimplemented;
        else {
          sendError(ErrorCode::invalidRequest, "ill-formed JSON request, expected array or object");
          continue;
        }
      }
    });
  }

  auto JsonRpcServer::handleRequest(nlohmann::json const& j) -> void {
    // Check if the the version number is present and correct
    if (!j.contains("jsonrpc") || j["jsonrpc"] != "2.0") unimplemented;

    // Determine the type of the message
    auto hasid = false;
    auto id = int64_t{};
    if (j.contains("id") && !j["id"].is_null()) {
      if (j["id"].is_string()) unimplemented;
      if (j["id"].is_number_integer()) {
        hasid = true;
        id = j["id"].get<int64_t>();
      }
    }

    // clang-format off
    if (j.contains("method") && j["method"].is_string()) {
      auto params = nlohmann::json();
      if (j.contains("params") && !j["params"].is_null()) {
        if (j["params"].is_array()) unimplemented;
        if (j["params"].is_object()) params = j["params"];
      }
      if (hasid) {
        // Request: method call
        auto const it = methods.find(j["method"]);
        if (it != methods.end()) {
          // Don't use captures, since they will be destroyed after lambda is destroyed...
          // See: https://en.cppreference.com/w/cpp/language/coroutines
          auto handler =
            [](
              JsonRpcServer* srv, int64_t id, std::function<Coroutine<nlohmann::json>(JsonRpcServer*, nlohmann::json)> func,
              nlohmann::json const& params
            ) -> Coroutine<void> {
            try {
              auto res = co_await func(srv, params);
              srv->sendResult(id, res);
            } catch (JsonRpcException& e) { srv->sendError(id, e.code, e.what()); } catch (std::exception& e) {
              // Using LSP methods to log the error
              srv->callNotification("window/logMessage", {
                {   "type",        1},
                {"message", e.what()}});
            }
          };
          handler(this, id, it->second, params);
        } else {
          sendError(id, ErrorCode::methodNotFound, "method \"" + std::string(j["method"]) + "\" not found");
        }
      } else {
        // Request: notification call
        auto const it = notifications.find(j["method"]);
        if (it != notifications.end()) {
          auto handler =
            [](
              JsonRpcServer* srv,
              std::function<Coroutine<void>(JsonRpcServer*, nlohmann::json)> func,
              nlohmann::json const& params
            ) -> Coroutine<void> {
            try {
              co_await func(srv, params);
            } catch (JsonRpcException& e) {
              // Using LSP methods to log the error
              srv->callNotification("window/logMessage", {
                {   "type",        1},
                {"message", e.what()}});
            } catch (std::exception& e) {
              // Using LSP methods to log the error
              srv->callNotification("window/logMessage", {
                {   "type",        1},
                {"message", e.what()}});
            }
          };
          handler(this, it->second, params);
        }
      }
    } else if (hasid && j.contains("result")) {
      // Response: result
      auto const it = requests.find(id);
      if (it != requests.end()) {
        it->second.result = j["result"];
        it->second.k.resume();
      }
      // Erase using `id` instead of `it`, as `requests` could have been modified by the coroutine
      requests.erase(id);
    } else if (j.contains("error") && j["error"].is_object() && j["error"].contains("code") && j["error"]["code"].is_number_integer()) {
      // Discard errors without ID, although they are allowed
      if (!hasid) return;
      // Response: error
      auto const it = requests.find(id);
      if (it != requests.end()) {
        auto const code = static_cast<ErrorCode>(j["error"]["code"].get<short>());
        auto const msg = j["error"].value("message", "");
        it->second.exptr = std::make_exception_ptr(JsonRpcException(code, msg));
        it->second.k.resume();
      }
      // Erase using `id` instead of `it`, as `requests` could have been modified by the coroutine
      requests.erase(id);
    } else {
      unimplemented;
    }
    // clang-format on
  }

  auto JsonRpcServer::send(nlohmann::json const& j) -> void {
    auto const s = j.dump();
    // See: https://microsoft.github.io/language-server-protocol/specifications/specification-current/#headerPart
    out << "Content-Length: " << s.size() << "\r\n";
    out << "Content-Type: " << contentType << "\r\n";
    out << "\r\n";
    out.write(s.data(), static_cast<std::streamsize>(s.size()));
    out.flush();
    /*
    log << ">> " << "Content-Length: " << s.size() << std::endl;
    log << ">> " << "Content-Type: " << CONTENT_TYPE_VALUE << std::endl;
    log << ">> " << s << std::endl << std::endl;
    */
  }

  auto JsonRpcServer::sendResult(int64_t id, nlohmann::json const& result) -> void {
    send({
      {"jsonrpc",  "2.0"},
      {     "id",     id},
      { "result", result}
    });
  }

  auto JsonRpcServer::sendError(ErrorCode code, std::string const& msg) -> void {
    send({
      {"jsonrpc",                              "2.0"},
      {     "id",                            nullptr},
      {  "error", {{"code", code}, {"message", msg}}}
    });
  }

  auto JsonRpcServer::sendError(int64_t id, ErrorCode code, std::string const& msg) -> void {
    send({
      {"jsonrpc",                              "2.0"},
      {     "id",                                 id},
      {  "error", {{"code", code}, {"message", msg}}}
    });
  }

#include "macros_close.hpp"
}
