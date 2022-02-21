#include <iostream>
#include <iomanip>
#include <utility>
#include <string>
#include <sstream>
#include <fstream>
#include <chrono>
#ifdef _WIN32
#include <fcntl.h>
#include <io.h>
#endif
#include <nlohmann/json.hpp>
#include "core/base.hpp"
#include "server/jsonrpc2.hpp"

using std::cin, std::cout, std::cerr, std::endl;
using std::pair, std::string, std::stringstream, nlohmann::json;
using Server::Coroutine, Server::JSONRPC2Exception, Server::JSONRPC2Server;


Coroutine<json> initialize(JSONRPC2Server*, const json&) {
  // This is a method.
  // We must send a response to it (`co_return` a json).
  co_return {
    {"capabilities", {
      // TODO: add server capabilities here
      {"hoverProvider", false},
    }},
    {"serverInfo", {
      {"name", "ApiMu Test Server"},
      {"version", "0.0.1"},
    }},
  };
}

Coroutine<json> test(JSONRPC2Server*, const json& params) {
  // This is a method with parameters (`params`).
  // We must send a response to it.
  co_return { {"echo", "Client said: " + params.value("str", "") + " Server replied: 喵喵喵🐱"} };
}

Coroutine<void> test1(JSONRPC2Server* srv, const json&) {
  // This is a notification.
  // We don't need to respond (we just `co_return` nothing), but we can send other requests:
  srv->callNotification("window/showMessage", {
    {"type", 2},
    {"message", string("Number of active coroutines: ") + std::to_string(Server::DebugCounter)}
  });
  co_return;
}

Coroutine<void> test2(JSONRPC2Server* srv, const json&) {
  // This is a notification.
  // We don't need to respond, but we can do other things:
  // Send request for user selection
  auto awaiter = srv->callMethod("window/showMessageRequest", {
    {"type", 3},
    {"message", "Select a severity level:"},
    {"actions", {
      { {"title", "Log"} },
      { {"title", "Info"} },
      { {"title", "Warning"} },
      { {"title", "Error"} }
    }}
  });
  // Suspend until a result arrives (this is where coroutines become useful!
  //   We can easily do asynchronous IO in a single thread.)
  json res = co_await awaiter;
  // Find out which option is selected...
  int sel = 0;
  if (res.contains("title") && res["title"].is_string()) {
    string s = res["title"];
    if (s == "Log") sel = 4;
    if (s == "Info") sel = 3;
    if (s == "Warning") sel = 2;
    if (s == "Error") sel = 1;
  }
  // Invalid response, discard
  if (sel == 0) co_return;
  // Valid response, put a message
  srv->callNotification("window/showMessage", {
    {"type", sel},
    {"message", "Hello world!"}
  });
  co_return;
}

Coroutine<json> shutdown(JSONRPC2Server*, const json&) {
  // This is a method.
  // According to spec, we must return a `null` result to it
  // (nlohmann::json uses `nullptr` or just `{}` to represent `null`.)
  co_return {};
}

Coroutine<void> exit_(JSONRPC2Server* srv, const json&) {
  // This is a notification.
  srv->requestStop();
  co_return;
}

// You may also throw certain exceptions (namely, of type `JSONRPC2Exception`) in methods:
//   throw JSONRPC2Exception(JSONRPC2Exception::SERVER_ERROR, "send out");
// This error information will get sent to the client.
// But if you throw other kinds of exceptions, or throw exceptions in notifications,
//   std::terminate() will be called (i.e. the program will crash).


int main() {
  // Windows automatically converts between "\r\n" and "\n" if cin/cout is in "text mode".
  // Change to "binary mode" disables this conversion. There is no standard (platform-independent) way of doing it [1].
  // On Unix systems there is no difference between "text mode" and "binary mode" [2].
  //   [1]: https://stackoverflow.com/questions/7587595/read-binary-data-from-stdcin
  //   [2]: https://stackoverflow.com/questions/25823310/is-there-any-difference-between-text-and-binary-mode-in-file-access
#ifdef _WIN32
  _setmode(_fileno(stdin), _O_BINARY);
  _setmode(_fileno(stdout), _O_BINARY);
#endif

  // Set up logging
  stringstream ss;
  ss << "log_" << std::chrono::system_clock::now().time_since_epoch().count() << ".txt";
  std::ofstream log(ss.str());

  // Create server
  Server::JSONRPC2Server srv(std::cin, std::cout, log);

  // The registered functions will be executed in one single thread!
  // So don't do any blocking (e.g. wait, sleep, cin >> s)...
  // Expensive computations (we don't have any yet) should be in separate threads too
  srv.addMethod       ("initialize", initialize);
  srv.addMethod       ("test",       test);
  srv.addNotification ("test1",      test1);
  srv.addNotification ("test2",      test2);
  srv.addMethod       ("shutdown",   shutdown);
  srv.addNotification ("exit",       exit_);

  // Start the server thread and wait until it was shut down...
  srv.startListen();
  srv.waitForComplete();
  log << "Server stopped." << std::endl;

  return 0;
}
