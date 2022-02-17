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

using std::cin, std::cout, std::cerr, std::endl;
using std::pair, std::string, nlohmann::json;
using jsonrpccxx::MethodHandle, jsonrpccxx::NotificationHandle;

std::ofstream out("D:/log.txt");


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

json test(const json& j) {
  json res = { { "echo", "Client said: " + j.value("str", "") + " Server replied: 喵喵喵🐱" } };
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
  std::getline(cin, res);
  if (!res.empty() && res.back() == '\r') res.pop_back();
  return res;
}

pair<string, string> split(const string& s) {
  size_t p = s.find(": ");
  if (p == string::npos) throw std::invalid_argument("No \": \" found in [" + s + "]");
  return { s.substr(0, p), s.substr(p + 2) };
}

int main() {
  jsonrpccxx::JsonRpc2Server rpcServer;

  rpcServer.Add("initialize", static_cast<MethodHandle>(initialize));
  rpcServer.Add("test", static_cast<MethodHandle>(test));
  rpcServer.Add("shutdown", static_cast<MethodHandle>(shutdown));
  rpcServer.Add("exit", static_cast<NotificationHandle>(exit_));

  // Windows automatically converts between "\r\n" and "\n" if cin/cout is in "text mode".
  // Change to "binary mode" disables this conversion. There is no standard (platform-independent) way of doing it [1].
  // On Unix systems there is no difference between "text mode" and "binary mode" [2].
  //   [1]: https://stackoverflow.com/questions/7587595/read-binary-data-from-stdcin
  //   [2]: https://stackoverflow.com/questions/25823310/is-there-any-difference-between-text-and-binary-mode-in-file-access
#ifdef _WIN32
	_setmode(_fileno(stdin), _O_BINARY);
	_setmode(_fileno(stdout), _O_BINARY);
#endif

  // Main loop
  while (true) {
    string s;

    // Read header part
    // See: https://microsoft.github.io/language-server-protocol/specifications/specification-current/#headerPart
    size_t n = 0;
    s = getline();
    while (s != "") {
      // We just disregard all header fields... except `Content-Length`!
      auto [key, value] = split(s);
      out << "[" << key << "] = [" << value << "]" << endl;
      if (key == "Content-Length") {
        std::stringstream ss(value);
        ss >> n;
      } else if (key == "Content-Type") {
        if (value != "application/vscode-jsonrpc; charset=utf-8")
          throw std::invalid_argument("Content-Type = " + value);
      } else throw std::invalid_argument("Key = " + key);
      // Get next line
      s = getline();
    }

    // End of header, get content
    s.resize(n);
    cin.read(s.data(), n);

    // Though LSP 3.16 says [1] that an Exit Notification after a Shutdown Request actually stops the server,
    // VSCode simply closes the input stream without giving an Exit Notification.
    // This line is used to stop the server in that case.
    //   [1]: https://microsoft.github.io/language-server-protocol/specifications/specification-3-17/#shutdown
    if (cin.eof()) std::exit(0);

    // Handle request
    out << "Request = [" << s << "]" << endl;
    s = rpcServer.HandleRequest(s);
    if (!s.empty()) {
      cout << "Content-Length: " << s.size() << "\r\n";
      cout << "Content-Type: application/vscode-jsonrpc; charset=utf-8\r\n";
      cout << "\r\n";
      cout.write(s.data(), s.size());
      cout.flush();
      // Debug output
      out << s << endl;
    }
    out << endl;
  }

  return 0;
}
