#include <iostream>
#include <utility>
#include <string>
#ifdef _WIN32
#include <fcntl.h>
#include <io.h>
#endif
#include "mu.hpp"
#include "server/languageserver.hpp"
#include "server/lsp.hpp"

using std::pair;
using std::string;
using std::vector;
using std::optional, std::make_optional, std::nullopt;
using nlohmann::json;
using Server::Coroutine, Server::JSONRPC2Exception, Server::JSONRPC2Server;
using Server::Document;
using namespace Server::LSP;


// =================
// Utility functions
// =================

void showMessage(JSONRPC2Server* srv, MessageType type, const string& msg) {
  srv->callNotification("window/showMessage", {
    {"type", static_cast<unsigned int>(type)},
    {"message", msg}
  });
}

void logMessage(JSONRPC2Server* srv, MessageType type, const string& msg) {
  srv->callNotification("window/logMessage", {
    {"type", static_cast<unsigned int>(type)},
    {"message", msg}
  });
}

Position fromIndex(const Document& doc, size_t index) {
  Document::Position p = doc.toUTF16(doc.toPosition(index));
  return { static_cast<unsigned int>(p.first), static_cast<unsigned int>(p.second) };
}

size_t toIndex(const Document& doc, Position pos) {
  Document::Position p = { pos.line, pos.character };
  return doc.toIndex(doc.toUTF8(p));
}

Range fromIndices(const Document& doc, size_t start, size_t end) {
  return { fromIndex(doc, start), fromIndex(doc, end) };
}

pair<size_t, size_t> toIndices(const Document& doc, Position start, Position end) {
  return { toIndex(doc, start), toIndex(doc, end) };
}


// ===========================
// Document analysis functions
// ===========================

struct Entry {
  Document doc{};
  AnalysisResult result{};
};

std::unordered_map<DocumentUri, Entry> docs;

void analyzeDocument(JSONRPC2Server* srv, const DocumentUri& uri) {
  Entry& e = docs[uri];
  const Document& doc = e.doc;
  string s = doc.getContent();
  vector<Diagnostic> res;

  Mu mu;
  mu.analyze(s);
  e.result = mu.popResults();

  for (const auto& ex: mu.popParsingErrors()) res.emplace_back(fromIndices(doc, ex.startPos, ex.endPos), ex.what(), DiagnosticSeverity::WARNING);
  for (const auto& ex: e.result.info) res.emplace_back(fromIndices(doc, ex.startPos, ex.endPos), ex.info, DiagnosticSeverity::INFORMATION);
  for (const auto& ex: e.result.errors) res.emplace_back(fromIndices(doc, ex.startPos, ex.endPos), ex.what(), DiagnosticSeverity::ERROR);
  for (auto& diag: res) diag.source = "Mu analyzer";

  srv->callNotification("textDocument/publishDiagnostics", {
    {"uri", uri},
    {"diagnostics", res}
  });
}


// ======================
// Server method handlers
// ======================

Coroutine<json> initialize(JSONRPC2Server*, const json&) {
  // This is a method.
  // We must send a response to it (`co_return` a json).
  co_return {
    {"capabilities", {
      {"textDocumentSync", {
        {"openClose", true},
        {"change", 2} // None: 0, full: 1, incremental: 2
      }},
      {"hoverProvider", true},
      {"definitionProvider", true},
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
  MessageType sel = MessageType::UNKNOWN;
  if (res.contains("title") && res["title"].is_string()) {
    string s = res["title"];
    if (s == "Log") sel = MessageType::LOG;
    if (s == "Info") sel = MessageType::INFO;
    if (s == "Warning") sel = MessageType::WARNING;
    if (s == "Error") sel = MessageType::ERROR;
  }
  // Invalid response, discard
  if (sel == MessageType::UNKNOWN) co_return;
  // Valid response, put a message
  showMessage(srv, sel, "Hello, world!");
  logMessage(srv, sel, "Hello, world!");
  co_return;
}

Coroutine<json> shutdown(JSONRPC2Server*, const json&) {
  // This is a method.
  // According to spec, we must return a `null` result to it
  // (nlohmann::json uses `nullptr` or just `{}` to represent `null`.)
  co_return {};
}

Coroutine<void> stop(JSONRPC2Server* srv, const json&) {
  // This is a notification.
  srv->requestStop();
  co_return;
}

Coroutine<void> didOpenTextDocument(JSONRPC2Server* srv, const json& params) {
  auto doc = params.at("textDocument").get<TextDocumentItem>();
  logMessage(srv, MessageType::LOG,
    "Text document opened: " + doc.uri
      + ", lang: " + (doc.languageId? *doc.languageId : "unknown")
      + ", version: " + (doc.version? std::to_string(*doc.version) : "unknown")
      + ", length: " + (doc.text? std::to_string(doc.text->size()) : "unknown"));
  if (doc.text) {
    docs[doc.uri].doc.setContent(*doc.text);
    analyzeDocument(srv, doc.uri);
  }
  co_return;
}

Coroutine<void> didChangeTextDocument(JSONRPC2Server* srv, const json& params) {
  auto doc = params.at("textDocument").get<TextDocumentItem>();
  logMessage(srv, MessageType::LOG,
    "Text document changed: " + doc.uri
      + ", lang: " + (doc.languageId? *doc.languageId : "unknown")
      + ", version: " + (doc.version? std::to_string(*doc.version) : "unknown")
      + ", length: " + (doc.text? std::to_string(doc.text->size()) : "unknown"));
  Document& d = docs[doc.uri].doc;
  auto changes = params.at("contentChanges").get<std::vector<TextDocumentContentChangeEvent>>();
  for (const auto& change: changes) {
    if (change.range) {
      Document::Position startRaw = { change.range->start.line, change.range->start.character };
      Document::Position endRaw = { change.range->end.line, change.range->end.character };
      size_t start = d.toIndex(d.toUTF8(startRaw));
      size_t end = d.toIndex(d.toUTF8(endRaw));
      d.modify(start, end, change.text);
    } else {
      d.setContent(change.text);
    }
  }
  // logMessage(srv, MessageType::LOG, "Current content:\n" + d.getContent());
  analyzeDocument(srv, doc.uri);
  co_return;
}

Coroutine<void> didCloseTextDocument(JSONRPC2Server* srv, const json& params) {
  auto doc = params.at("textDocument").get<TextDocumentItem>();
  logMessage(srv, MessageType::LOG,
    "Text document closed: " + doc.uri
      + ", lang: " + (doc.languageId? *doc.languageId : "unknown")
      + ", version: " + (doc.version? std::to_string(*doc.version) : "unknown")
      + ", length: " + (doc.text? std::to_string(doc.text->size()) : "unknown"));
  docs.erase(doc.uri);
  co_return;
}

Coroutine<json> hover(JSONRPC2Server* srv, const json& params) {
  auto doc = params.at("textDocument").get<TextDocumentIdentifier>();
  auto pos = params.at("position").get<Position>();
  logMessage(srv, MessageType::LOG,
    "Hover at " + doc.uri + ", " + std::to_string(pos.line) + ":" + std::to_string(pos.character));
  const Entry& e = docs[doc.uri];
  size_t index = toIndex(e.doc, pos);
  auto& hovers = e.result.hovers;
  for (const auto& hover: hovers) if (hover.startPos <= index && hover.endPos >= index) {
    json c = { hover.info, MarkedString{ "apimu", hover.code } };
    if (hover.info.empty()) c = c[1]; else if (hover.code.empty()) c = c[0];
    co_return {
      {"contents", c},
      {"range", fromIndices(e.doc, hover.startPos, hover.endPos)}
    };
  }
  co_return {};
}

Coroutine<json> definition(JSONRPC2Server* srv, const json& params) {
  auto doc = params.at("textDocument").get<TextDocumentIdentifier>();
  auto pos = params.at("position").get<Position>();
  logMessage(srv, MessageType::LOG,
    "Query definition at " + doc.uri + ", " + std::to_string(pos.line) + ":" + std::to_string(pos.character));
  const Entry& e = docs[doc.uri];
  size_t index = toIndex(e.doc, pos);
  auto& tokens = e.result.tokens;
  for (const auto& token: tokens) if (token.startPos <= index && token.endPos >= index) {
    if (!token.defPos) continue;
    co_return Location{ doc.uri, fromIndices(e.doc, token.defPos->first, token.defPos->second) };
  }
  co_return {};
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

  /*
  // Set up logging
  stringstream ss;
  ss << "log_" << std::chrono::system_clock::now().time_since_epoch().count() << ".txt";
  std::ofstream log(ss.str());
  */

  // Create server
  Server::JSONRPC2Server srv(std::cin, std::cout /*, log */);

  // The registered functions will be executed in one single thread!
  // So don't do any blocking (e.g. wait, sleep, cin >> s)...
  // Expensive computations (we don't have any yet) should be in separate threads too
  srv.addMethod       ("initialize", initialize);
  srv.addMethod       ("test", test);
  srv.addNotification ("test1", test1);
  srv.addNotification ("test2", test2);
  srv.addMethod       ("shutdown", shutdown);
  srv.addNotification ("exit", stop);
  srv.addNotification ("textDocument/didOpen", didOpenTextDocument);
  srv.addNotification ("textDocument/didChange", didChangeTextDocument);
  srv.addNotification ("textDocument/didClose", didCloseTextDocument);
  srv.addMethod       ("textDocument/hover", hover);
  srv.addMethod       ("textDocument/definition", definition);

  // Start the server thread and wait until it was shut down...
  srv.startListen();
  srv.waitForComplete();
  // log << "Server stopped." << std::endl;

  return 0;
}
