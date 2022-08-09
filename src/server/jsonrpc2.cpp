#include "jsonrpc2.hpp"
#include <iostream>
#include <optional>

namespace Server {

  using std::optional, std::nullopt;

  void JSONRPC2Server::callNotification(const string& method, const json& params) {
    send({
      {"jsonrpc",  "2.0"},
      { "method", method},
      { "params", params}
    });
  }

  JSONRPC2Server::RequestAwaiter JSONRPC2Server::callMethod(const string& method, const json& params) {
    RequestAwaiter res{this, nextid};
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
  const string CONTENT_TYPE_VALUE = "application/vscode-jsonrpc; charset=utf-8";

  // Returns `nullopt` if read past EOF.
  // For discussions on non-blocking `cin`, see:
  // https://stackoverflow.com/questions/16592357/non-blocking-stdgetline-exit-if-no-input The following code uses
  // blocking input, which is enough for the current purpose.
  optional<string> JSONRPC2Server::readNextPacket() {

    // `std::getline()` and then trim trailing "\r\n"
    // ("\r\n" is used as EOL in LSP 3.16 header part)
    auto getline = [this]() {
      string res = "";
      std::getline(in, res);
      if (!res.empty() && res.back() == '\r') res.pop_back();
      return res;
    };

    // Read header part
    size_t n = 0;
    string s = getline();

    while (s != "") {
      size_t p = s.find(": ");
      if (p == string::npos) notimplemented;
      string key = s.substr(0, p), value = s.substr(p + 2);
      // log << "<< \"" << key << "\" = \"" << value << "\"" << std::endl;

      if (key == "Content-Length") {
        std::stringstream ss(value);
        ss >> n;
      } else if (key == "Content-Type") {
        if (value != CONTENT_TYPE_VALUE) notimplemented;
      } else notimplemented;

      // Get next line
      s = getline();
    }

    // End of header, get content
    s.resize(n);
    in.read(s.data(), n);
    // log << "<< " << s << std::endl << std::endl;

    if (in.eof()) return nullopt;
    return s;
  }

  void JSONRPC2Server::startListen() {

    // Start the listener thread (`inThread`)
    // For an example of using `std::jthread`, see: https://en.cppreference.com/w/cpp/thread/stop_token
    inThread = std::jthread([this](std::stop_token stopToken) {
      // Main loop
      while (!stopToken.stop_requested()) {
        optional<string> o = readNextPacket();

        // Though LSP 3.16 says [1] that an Exit Notification after a Shutdown Request actually stops the server,
        // VSCode simply closes the input stream without giving an Exit Notification.
        // This line is used to stop the input listener thread in that case.
        //   [1]: https://microsoft.github.io/language-server-protocol/specifications/specification-3-16/#shutdown
        if (!o.has_value()) break;

        // Parse JSON-RPC 2.0 requests/notifications
        json j;
        try {
          j = json::parse(*o);
        } catch (json::parse_error& e) {
          sendError(PARSE_ERROR, e.what());
          continue;
        }

        // Handle JSON request
        if (j.is_object()) handleRequest(j);
        else if (j.is_array()) notimplemented;
        else {
          sendError(INVALID_REQUEST, "ill-formed JSON request, expected array or object");
          continue;
        }
      }
    });
  }

  void JSONRPC2Server::handleRequest(const json& j) {

    // Check if the the version number is present and correct
    if (!j.contains("jsonrpc") || j["jsonrpc"] != "2.0") notimplemented;

    // Determine the type of the message
    bool hasid = false;
    int64_t id;
    if (j.contains("id") && !j["id"].is_null()) {
      if (j["id"].is_string()) notimplemented;
      if (j["id"].is_number_integer()) {
        hasid = true;
        id = j["id"].get<int64_t>();
      }
    }

    if (j.contains("method") && j["method"].is_string()) {
      json params;
      if (j.contains("params") && !j["params"].is_null()) {
        if (j["params"].is_array()) notimplemented;
        if (j["params"].is_object()) params = j["params"];
      }
      if (hasid) {
        // Request: method call
        auto it = methods.find(j["method"]);
        if (it != methods.end()) {
          // Don't use captures, since they will be destroyed after lambda is destroyed...
          // See: https://en.cppreference.com/w/cpp/language/coroutines
          auto handler = [](
                           JSONRPC2Server* srv, int id, std::function<Coroutine<json>(JSONRPC2Server*, json)> func,
                           const json& params
                         ) -> Coroutine<void> {
            try {
              json res = co_await func(srv, params);
              srv->sendResult(id, res);
            } catch (const JSONRPC2Exception& e) {
              srv->sendError(id, e.code, e.what());
            } catch (const std::exception& e) {
              // Using LSP methods to log the error
              srv->callNotification(
                "window/logMessage",
                {
                  {   "type",        1},
                  {"message", e.what()}
              }
              );
            }
          };
          handler(this, id, it->second, params);
        } else {
          sendError(id, METHOD_NOT_FOUND, "method \"" + string(j["method"]) + "\" not found");
        }
      } else {
        // Request: notification call
        auto it = notifications.find(j["method"]);
        if (it != notifications.end()) {
          auto handler = [](
                           JSONRPC2Server* srv, std::function<Coroutine<void>(JSONRPC2Server*, json)> func,
                           const json& params
                         ) -> Coroutine<void> {
            try {
              co_await func(srv, params);
            } catch (const JSONRPC2Exception& e) {
              // Using LSP methods to log the error
              srv->callNotification(
                "window/logMessage",
                {
                  {   "type",        1},
                  {"message", e.what()}
              }
              );
            } catch (const std::exception& e) {
              // Using LSP methods to log the error
              srv->callNotification(
                "window/logMessage",
                {
                  {   "type",        1},
                  {"message", e.what()}
              }
              );
            }
          };
          handler(this, it->second, params);
        }
      }

    } else if (hasid && j.contains("result")) {
      // Response: result
      auto it = requests.find(id);
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
      auto it = requests.find(id);
      if (it != requests.end()) {
        ErrorCode code = static_cast<ErrorCode>(j["error"]["code"].get<short>());
        string msg = j["error"].value("message", "");
        it->second.exptr = std::make_exception_ptr(JSONRPC2Exception(code, msg));
        it->second.k.resume();
      }
      // Erase using `id` instead of `it`, as `requests` could have been modified by the coroutine
      requests.erase(id);

    } else notimplemented;
  }

  void JSONRPC2Server::send(const json& j) {
    string s = j.dump();
    // See: https://microsoft.github.io/language-server-protocol/specifications/specification-current/#headerPart
    out << "Content-Length: " << s.size() << "\r\n";
    out << "Content-Type: " << CONTENT_TYPE_VALUE << "\r\n";
    out << "\r\n";
    out.write(s.data(), s.size());
    out.flush();
    /*
    log << ">> " << "Content-Length: " << s.size() << std::endl;
    log << ">> " << "Content-Type: " << CONTENT_TYPE_VALUE << std::endl;
    log << ">> " << s << std::endl << std::endl;
    */
  }

  void JSONRPC2Server::sendResult(int64_t id, const json& result) {
    send({
      {"jsonrpc",  "2.0"},
      {     "id",     id},
      { "result", result}
    });
  }

  void JSONRPC2Server::sendError(ErrorCode code, const string& msg) {
    send({
      {"jsonrpc",                              "2.0"},
      {     "id",                            nullptr},
      {  "error", {{"code", code}, {"message", msg}}}
    });
  }

  void JSONRPC2Server::sendError(int64_t id, ErrorCode code, const string& msg) {
    send({
      {"jsonrpc",                              "2.0"},
      {     "id",                                 id},
      {  "error", {{"code", code}, {"message", msg}}}
    });
  }

}
