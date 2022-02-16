#include <iostream>
#include <iomanip>
#include <utility>
#include <string>
#include <sstream>
#include <fstream>
#ifdef _WIN32
#include <fcntl.h>
#include <io.h>
#endif
#include <jsonrpccxx/server.hpp>
#include "core/base.hpp"

using std::cin, std::cout, /* std::cerr, */ std::endl;
using std::pair, std::string, nlohmann::json;
using jsonrpccxx::MethodHandle, jsonrpccxx::NotificationHandle;

std::ofstream cerr("D:/log.txt");


json initialize(const json&) {
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
  return res;
}

void initialized(const json&) {}

json test(const json& j) {
  json res = { { "echo", j.value("str", "") } };
  return res;
}

json shutdown(const json&) {
  json res = {};
  return res;
}

void exit_(const json&) {
  std::exit(0);
}


string getline() {
  string res = "";
///*
  std::getline(cin, res);
  if (!res.empty() && res.back() == '\r') res.pop_back();
  cerr << "Got [" << res << "] " << std::boolalpha << cin.eof() << endl;
  return res;
//*/
/*
  char c = static_cast<char>(cin.get());
  while (c != std::ios::traits_type::eof() && c != '\r' && c != '\n') {
    res += c;
    c = static_cast<char>(cin.get());
  }
  if (c == '\r') cin.ignore(); // Ignore "\n" after "\r"
  cerr << "Got [" << res << "] " << std::boolalpha << cin.eof() << endl;
  return res;
*/
}

pair<string, string> split(const string& s) {
  size_t p = s.find(": ");
  if (p == string::npos) throw std::logic_error("No \": \" found in [" + s + "]"); // ???
  return { s.substr(0, p), s.substr(p + 2) };
}

int main() {
  jsonrpccxx::JsonRpc2Server rpcServer;

  rpcServer.Add("initialize", static_cast<MethodHandle>(initialize));
  rpcServer.Add("initialized", static_cast<NotificationHandle>(initialized));
  rpcServer.Add("test", static_cast<MethodHandle>(test));
  rpcServer.Add("shutdown", static_cast<MethodHandle>(shutdown));
  rpcServer.Add("exit", static_cast<NotificationHandle>(exit_));

  // ???
#ifdef _WIN32
	_setmode(_fileno(stdin), _O_BINARY);
	_setmode(_fileno(stdout), _O_BINARY);
#endif

  // Main loop
  while (true) {
    string s;
    // Read header part
    // https://microsoft.github.io/language-server-protocol/specifications/specification-current/#headerPart
    size_t n = 0;
    s = getline();
    while (s != "") {
      // We just disregard all header fields... except `Content-Length`!
      auto [key, value] = split(s);
      cerr << "[" << key << "] = [" << value << "]" << endl;
      if (key == "Content-Length") {
        std::stringstream ss(value);
        ss >> n;
      } else if (key == "Content-Type") {
        if (value != "application/vscode-jsonrpc; charset=utf-8" &&
            value != "application/vscode-jsonrpc; charset=utf8")
          throw std::logic_error("Content-Type = " + value);
      } else throw std::logic_error("Key = " + key);
      // Get next line
      s = getline();
    }
    // End of header, get content
    s.resize(n);
    cin.read(s.data(), n);
    if (cin.eof()) std::exit(0); // ???
    // Handle request
    cerr << "Request = [" << s << "]" << endl;
    s = rpcServer.HandleRequest(s);
    if (!s.empty()) {
      cout << "Content-Length: " << s.size() << "\r\n";
      cout << "Content-Type: application/vscode-jsonrpc; charset=utf-8\r\n";
      cout << "\r\n";
      cout.write(s.data(), s.size());
      cout.flush();
      // Debug output
      cerr << "Content-Length: " << s.size() << endl;
      cerr << "Content-Type: application/vscode-jsonrpc; charset=utf-8" << endl;
      cerr << endl;
      cerr << s << endl << endl;
    }
  }

  return 0;
}
