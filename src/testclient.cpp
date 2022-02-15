#include <jsonrpccxx/common.hpp>
#include <jsonrpccxx/client.hpp>
#include <cpp-httplib/httplib.h>


// Adapted from: https://github.com/jsonrpcx/json-rpc-cxx/tree/master/examples
class HttpClientConnector: public jsonrpccxx::IClientConnector {
public:
  explicit HttpClientConnector(const std::string &host, int port):
           httpClient(host.c_str(), port) {}

  // Sends request and returns response
  std::string Send(const std::string &request) override {
    auto res = httpClient.Post("/jsonrpc", request, "application/json");
    if (!res || res->status != 200) {
      throw jsonrpccxx::JsonRpcException(-32003, "client connector error, received status != 200");
    }
    return res->body;
  }

private:
  httplib::Client httpClient;
};


int main() {
  
  return 0;
}
