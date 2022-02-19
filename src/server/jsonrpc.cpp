#include "jsonrpc.hpp"
#include <core/base.hpp>


namespace Server {

  // This implementation is written against LSP 3.16 and JSON-RPC 2.0
  // See: https://microsoft.github.io/language-server-protocol/specifications/specification-current/#headerPart
  // See: https://www.jsonrpc.org/specification

  // The only supported value for Content-Type
  const string CONTENT_TYPE_VALUE = "application/vscode-jsonrpc; charset=utf-8";

  void JSONRPC2Connection::startListen() {
    // Start the listener thread (`inThread`)
    inThread = std::jthread([this] (std::stop_token stopToken) {
      // For an example of using `std::jthread`, see: https://en.cppreference.com/w/cpp/thread/stop_token
      // For discussions on non-blocking `cin`, see: https://stackoverflow.com/questions/16592357/non-blocking-stdgetline-exit-if-no-input
      // The following code uses blocking input, which is enough for the current purpose.

      // `std::getline()` and then trim trailing "\r\n" ("\r\n" is used as EOL in LSP 3.16 header part)
      auto getline = [this] () {
        string res = "";
        std::getline(in, res);
        if (!res.empty() && res.back() == '\r') res.pop_back();
        return res;
      };

      // Main loop
      while (!stopToken.stop_requested()) {
        string s;

        // Read header part
        size_t n = 0;
        s = getline();

        while (s != "") {
          size_t p = s.find(": ");
          if (p == string::npos)
            throw Core::NotImplemented("unexpected line in JSON-RPC header, no \": \" found in \"" + s + "\"");
          string key = s.substr(0, p), value = s.substr(p + 2);
          {
            std::scoped_lock<std::mutex> lock(logLock);
            log << "<< \"" << key << "\" = \"" << value << "\"" << std::endl;
          }

          if (key == "Content-Length") {
            std::stringstream ss(value);
            ss >> n;
          } else if (key == "Content-Type") {
            if (value != CONTENT_TYPE_VALUE)
              throw Core::NotImplemented("unexpected \"Content-Type\" value in JSON-RPC header: \"" + value + "\"");
          } else {
            throw Core::NotImplemented("unexpected key in JSON-RPC header: \"" + key + "\"");
          }

          // Get next line
          s = getline();
        }

        // End of header, get content
        s.resize(n);
        in.read(s.data(), n);
        {
          std::scoped_lock<std::mutex> lock(logLock);
          log << "<< " << s << std::endl << std::endl;
        }

        // Though LSP 3.16 says [1] that an Exit Notification after a Shutdown Request actually stops the server,
        // VSCode simply closes the input stream without giving an Exit Notification.
        // This line is used to stop the input listener thread in that case.
        //   [1]: https://microsoft.github.io/language-server-protocol/specifications/specification-3-16/#shutdown
        if (in.eof()) break;

        // Parse JSON-RPC 2.0 requests/notifications
        json j;
        try {
          j = json::parse(s);
        } catch (json::parse_error &e) {
          sendError<PARSE_ERROR>(e.what());
          continue;
        }

        // Handle JSON request
        if (j.is_object()) handleRequest(j);
        else if (j.is_array()) throw Core::NotImplemented("batch requests in JSON-RPC is not supported yet");
        else { sendError<INVALID_REQUEST>("ill-formed JSON request, expected array or object"); continue; }
      }
    });
  }

  void JSONRPC2Connection::handleRequest(const json& j) {
    // Check if the the version number is present and correct
    if (!j.contains("jsonrpc") || j["jsonrpc"] != "2.0")
      throw Core::NotImplemented("only JSON-RPC 2.0 is supported");

    // Determine the type of the message
    bool hasid = false;
    int id;
    if (j.contains("id") && !j["id"].is_null()) {
      if (j["id"].is_string()) throw Core::NotImplemented("string-typed `id` in JSON-RPC is not supported yet");
      if (j["id"].is_number()) {
        hasid = true;
        id = j["id"].get<int>();
      }
    }
    if (j.contains("method") && j["method"].is_string()) {
      json params;
      if (j.contains("params") && !j["params"].is_null()) {
        if (j["params"].is_array()) throw Core::NotImplemented("array-typed `params` in JSON-RPC is not supported yet");
        if (j["params"].is_object()) params = j["params"];
      }
      if (hasid) {
        // Request: method call
        auto it = methods.find(j["method"]);
        if (it != methods.end()) {
          // TODO: use exceptions for error?
          it->second(this, id, params);
        } else {
          sendError<METHOD_NOT_FOUND>(id, "method \"" + string(j["method"]) + "\"not found");
        }
      } else {
        // Request: notification call
        auto it = notifications.find(j["method"]);
        if (it != notifications.end()) {
          // TODO: use exceptions for error?
          it->second(this, params);
        }
      }
    } else if (j.contains("result")) {
      if (!hasid) return;
      // Response: result
      auto it = promises.find(id);
      if (it != promises.end()) {
        it->second.set_value(j["result"]);
      }
    } else if (j.contains("error")) {
      if (!hasid) return;
      // Response: error
      auto it = promises.find(id);
      if (it != promises.end()) {
        // TODO: use exceptions for error?
        // it->second.set_exception();
        it->second.set_value(nullptr);
      }
    } else {
      throw Core::NotImplemented("unknown JSON-RPC message type");
    }
  }

  void JSONRPC2Connection::send(const json& j) {
    string s = j.dump();
    // Ensure that calling from different threads will not result in broken packets
    std::scoped_lock<std::mutex> lock(outLock);
    // See: https://microsoft.github.io/language-server-protocol/specifications/specification-current/#headerPart
    out << "Content-Length: " << s.size() << "\r\n";
    out << "Content-Type: " << CONTENT_TYPE_VALUE << "\r\n";
    out << "\r\n";
    out.write(s.data(), s.size());
    out.flush();
    {
      std::scoped_lock<std::mutex> lock(logLock);
      log << ">> " << "Content-Length: " << s.size() << std::endl;
      log << ">> " << "Content-Type: " << CONTENT_TYPE_VALUE << std::endl;
      log << ">> " << s << std::endl << std::endl;
    }
  }

  std::future<json> JSONRPC2Connection::callMethod(const string& method, const json& params) {
    auto res = promises.emplace(nextid, std::promise<json>()).first->second.get_future();
    send({{ "jsonrpc", "2.0" }, { "id", nextid }, { "method", method }, { "params", params }});
    nextid++;
    return res;
  }
}
