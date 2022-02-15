#include <iostream>
#include <iomanip>
#include <string>
#include <jsonrpccxx/server.hpp>
#include <cpp-httplib/httplib.h>


// Adapted from: https://github.com/jsonrpcx/json-rpc-cxx/tree/master/examples
class HttpServerConnector {
public:
  explicit HttpServerConnector(jsonrpccxx::JsonRpcServer& rpcServer, const std::string& host, int port):
           thread(), httpServer(), rpcServer(rpcServer), host(host), port(port) {
    // Handles POST requests to `/jsonrpc`
    httpServer.Post("/jsonrpc", [this] (const httplib::Request& req, httplib::Response& res) {
      postAction(req, res);
    });
  }
  virtual ~HttpServerConnector() { stopListening(); }

  bool startListening() {
    if (httpServer.is_running()) return false; // Already started
    thread = std::thread([this] () { httpServer.listen(host.c_str(), port); });
    return true;
  }

  void stopListening() {
    if (!httpServer.is_running()) return;
    httpServer.stop();
    thread.join();
  }

private:
  std::thread thread;
  httplib::Server httpServer;
  jsonrpccxx::JsonRpcServer& rpcServer;

  std::string host;
  int port;

  void postAction(const httplib::Request& req, httplib::Response& res) {
    // Writes response using `rpcServer`
    res.status = 200;
    res.set_content(this->rpcServer.HandleRequest(req.body), "application/json");
  }
};


using std::cin, std::cout, std::endl;
using std::string;

int main() {
  jsonrpccxx::JsonRpc2Server rpcServer;
  std::function<string(const string&)> func = [] (const string& s) { return s; };
  rpcServer.Add("test", jsonrpccxx::GetHandle(func), { "param_name" });

  HttpServerConnector httpServer(rpcServer, "localhost", 8484);
  cout << "Starting HTTP server: " << std::boolalpha << httpServer.startListening() << endl;
  cout << "Enter 0 to exit" << endl;

  while (true) {
    int in;
    cin >> in;
    if (in == 0) break;
  }
  return 0;
}
