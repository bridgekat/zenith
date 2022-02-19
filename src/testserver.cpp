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
#include "server/jsonrpc.hpp"

using std::cin, std::cout, std::cerr, std::endl;
using std::pair, std::string, nlohmann::json;
using Server::JSONRPC2Connection;


void initialize(JSONRPC2Connection* srv, int id, const json&) {
  json res = {
    { "capabilities", {
      // TODO: add server capabilities here
      { "hoverProvider", false },
    } },
    { "serverInfo", {
      { "name", "ApiMu Test Server" },
      { "version", "0.0.1" },
    } },
  };
  srv->sendResult(id, res);
}

void test(JSONRPC2Connection* srv, int id, const json& j) {
  json res = { { "echo", "Client said: " + j.value("str", "") + " Server replied: 喵喵喵🐱" } };
  srv->sendResult(id, res);
}

void test1(JSONRPC2Connection* srv, const json&) {
  json showmsg = {
    { "type", 2 },
    { "message", "This is a warning!" }
  };
  srv->callNotification("window/showMessage", showmsg);
}

void shutdown(JSONRPC2Connection* srv, int id, const json&) {
  json res = {};
  srv->sendResult(id, res);
}

void exit_(JSONRPC2Connection*, const json&) {
  std::exit(0);
}


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

  std::stringstream ss;
  ss << "log_" << std::chrono::system_clock::now().time_since_epoch().count() << ".txt";
  std::ofstream log(ss.str());
  Server::JSONRPC2Connection conn(std::cin, std::cout, log);

  // The registered functions will be executed in the listener thread! So don't do any blocking...
  conn.methods.emplace("initialize", initialize);
  conn.methods.emplace("test", test);
  conn.notifications.emplace("test1", test1);
  conn.methods.emplace("shutdown", shutdown);
  conn.notifications.emplace("exit", exit_);

  // Start the listener thread...
  conn.startListen();
  conn.waitForComplete();
  log << "Server stopped." << std::endl;

  return 0;
}
