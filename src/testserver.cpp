#include <iostream>
#include <string>
#include <utility>
#ifdef _WIN32
#  include <fcntl.h>
#  include <io.h>
#endif
#include <core/expr.hpp>
#include <core/fol/fol.hpp>
#include <eval/extended_evaluator.hpp>
#include <eval/tree.hpp>
#include <server/document.hpp>
#include <server/lsp.hpp>

using nlohmann::json;
using namespace apimu;
using namespace server::lsp;
using server::Coroutine, server::JsonRpcException, server::JsonRpcServer, server::Document;

// =================
// Utility functions
// =================

auto showMessage(JsonRpcServer* srv, MessageType type, std::string const& msg) -> void {
  srv->callNotification(
    "window/showMessage",
    {
      {   "type", static_cast<unsigned int>(type)},
      {"message",                             msg}
  }
  );
}

auto logMessage(JsonRpcServer* srv, MessageType type, std::string const& msg) -> void {
  srv->callNotification(
    "window/logMessage",
    {
      {   "type", static_cast<unsigned int>(type)},
      {"message",                             msg}
  }
  );
}

auto fromIndex(Document const& doc, size_t index) -> Position {
  auto const p = doc.toUtf16(doc.toPosition(index));
  return {static_cast<unsigned int>(p.first), static_cast<unsigned int>(p.second)};
}

auto toIndex(Document const& doc, Position pos) -> size_t {
  auto const p = Document::Position{pos.line, pos.character};
  return doc.toIndex(doc.toUtf8(p));
}

auto fromIndices(Document const& doc, size_t start, size_t end) -> Range {
  return {fromIndex(doc, start), fromIndex(doc, end)};
}

auto toIndices(Document const& doc, Position start, Position end) -> std::pair<size_t, size_t> {
  return {toIndex(doc, start), toIndex(doc, end)};
}

// ===========================
// Document analysis functions
// ===========================

struct Entry {
  Document document;
  std::optional<std::jthread> thread;
};

// NOLINTNEXTLINE(cppcoreguidelines-avoid-non-const-global-variables)
auto entries = std::unordered_map<DocumentUri, Entry>();

auto startAnalysis(JsonRpcServer* srv, DocumentUri uri) -> void {
  entries[uri].thread.emplace([srv, uri](std::stop_token stopToken) {
    auto const& doc = entries[uri].document;
    auto const& s = doc.getContent();
    auto diags = std::vector<Diagnostic>();

    auto evaluator = eval::ExtendedEvaluator();
    evaluator.setString(s);

    while (!evaluator.eof()) {
      if (stopToken.stop_requested())
        return;
      auto const& res = evaluator.evalNextStatement();
      if (res) {
        auto const& [expr, begin, end] = *res;
        auto const str = expr->toString();
        auto const severity = (str == "#unit") ? DiagnosticSeverity::hint : DiagnosticSeverity::information;
        diags.emplace_back(Diagnostic{fromIndices(doc, begin, end), str, severity});
      }
    }
    for (auto const& [error, desc, begin, end]: evaluator.messages()) {
      auto const severity = error ? DiagnosticSeverity::error : DiagnosticSeverity::information;
      diags.emplace_back(Diagnostic{fromIndices(doc, begin, end), desc, severity});
    }

    // Analysis completed.
    srv->callNotification(
      "textDocument/publishDiagnostics",
      {
        {        "uri",   uri},
        {"diagnostics", diags}
    }
    );
  });
}

// ======================
// Server method handlers
// ======================

auto initialize(JsonRpcServer*, json const&) -> Coroutine<json> {
  // This is a method.
  // We must send a response to it (`co_return` a json).
  co_return {
    {"capabilities",
     {
     {"textDocumentSync",
     {
     {"openClose", true},
     {"change", 2} // None: 0, full: 1, incremental: 2
     }},
     // {"hoverProvider", true},
     // {"definitionProvider", true},
     }},
    {  "serverInfo",
     {
     {"name", "ApiMu Test Server"},
     {"version", "0.1.0"},
     }},
  };
}

auto test1(JsonRpcServer*, json const& params) -> Coroutine<json> {
  // This is a method with parameters (`params`).
  // We must send a response to it.
  co_return {
    {"echo", "Client said: " + params.value("str", "") + " Server replied: 喵喵喵🐱"}
  };
}

auto test2(JsonRpcServer* srv, json const&) -> Coroutine<void> {
  // This is a notification.
  // We don't need to respond, but we can do other things:
  // Send request for user selection
  auto awaitable = srv->callMethod(
    "window/showMessageRequest",
    {
      {   "type",                                                                                       3},
      {"message",                                                              "Select a severity level:"},
      {"actions", {{{"title", "Log"}}, {{"title", "Info"}}, {{"title", "Warning"}}, {{"title", "Error"}}}}
  }
  );
  // Suspend until a result arrives (this is where coroutines become useful!
  //   We can easily do asynchronous IO in a single thread.)
  auto res = co_await awaitable;
  // Find out which option is selected...
  auto sel = MessageType::unknown;
  if (res.contains("title") && res["title"].is_string()) {
    auto s = res["title"];
    if (s == "Log")
      sel = MessageType::log;
    if (s == "Info")
      sel = MessageType::info;
    if (s == "Warning")
      sel = MessageType::warning;
    if (s == "Error")
      sel = MessageType::error;
  }
  // Invalid response, discard
  if (sel == MessageType::unknown)
    co_return;
  // Valid response, put a message
  showMessage(srv, sel, "Hello, world!");
  logMessage(srv, sel, "Hello, world!");
  co_return;
}

auto shutdown(JsonRpcServer*, json const&) -> Coroutine<json> {
  // This is a method.
  // According to spec, we must return a `null` result to it
  // (nlohmann::json uses `{}` to represent `null`.)
  co_return {};
}

auto stop(JsonRpcServer* srv, json const&) -> Coroutine<void> {
  // This is a notification.
  entries.clear();
  srv->requestStop();
  co_return;
}

auto didOpenTextDocument(JsonRpcServer* srv, json const& params) -> Coroutine<void> {
  auto const d = params.at("textDocument").get<TextDocumentItem>();
  logMessage(
    srv,
    MessageType::log,
    "Text document opened: " + d.uri + ", lang: " + (d.languageId ? *d.languageId : "unknown")
      + ", version: " + (d.version ? std::to_string(*d.version) : "unknown")
      + ", length: " + (d.text ? std::to_string(d.text->size()) : "unknown")
  );
  if (d.text) {
    entries[d.uri].thread.reset();
    entries[d.uri].document.setContent(*d.text);
    startAnalysis(srv, d.uri);
  }
  co_return;
}

auto didChangeTextDocument(JsonRpcServer* srv, json const& params) -> Coroutine<void> {
  auto const d = params.at("textDocument").get<TextDocumentItem>();
  logMessage(
    srv,
    MessageType::log,
    "Text document changed: " + d.uri + ", lang: " + (d.languageId ? *d.languageId : "unknown")
      + ", version: " + (d.version ? std::to_string(*d.version) : "unknown")
      + ", length: " + (d.text ? std::to_string(d.text->size()) : "unknown")
  );
  entries[d.uri].thread.reset();
  auto& doc = entries[d.uri].document;
  auto const changes = params.at("contentChanges").get<std::vector<TextDocumentContentChangeEvent>>();
  for (auto const& change: changes) {
    if (change.range) {
      auto const startRaw = Document::Position{change.range->start.line, change.range->start.character};
      auto const endRaw = Document::Position{change.range->end.line, change.range->end.character};
      auto const start = doc.toIndex(doc.toUtf8(startRaw));
      auto const end = doc.toIndex(doc.toUtf8(endRaw));
      doc.modify(start, end, change.text);
    } else {
      doc.setContent(change.text);
    }
  }
  // logMessage(srv, MessageType::LOG, "Current content:\n" + d.getContent());
  startAnalysis(srv, d.uri);
  co_return;
}

auto didCloseTextDocument(JsonRpcServer* srv, json const& params) -> Coroutine<void> {
  auto const d = params.at("textDocument").get<TextDocumentItem>();
  logMessage(
    srv,
    MessageType::log,
    "Text document closed: " + d.uri + ", lang: " + (d.languageId ? *d.languageId : "unknown")
      + ", version: " + (d.version ? std::to_string(*d.version) : "unknown")
      + ", length: " + (d.text ? std::to_string(d.text->size()) : "unknown")
  );
  entries.erase(d.uri);
  co_return;
}

/*
auto hover(JsonRpcServer* srv, json const& params) -> Coroutine<json> {
  auto const d = params.at("textDocument").get<TextDocumentIdentifier>();
  auto const p = params.at("position").get<Position>();
  logMessage(
    srv,
    MessageType::log,
    "Hover at " + d.uri + ", " + std::to_string(p.line) + ":" + std::to_string(p.character)
  );
  auto const& e = docs[d.uri];
  auto const index = toIndex(e, p);
  auto& hovers = e.result.hovers;
  for (const auto& hover: hovers)
    if (hover.begin <= index && hover.end >= index) {
      json c = {
        hover.info,
        MarkedString{"apimu", hover.code}
      };
      if (hover.info.empty()) c = c[1];
      else if (hover.code.empty()) c = c[0];
      co_return {
        {"contents", c},
        {"range", fromIndices(e.doc, hover.begin, hover.end)}
      };
    }
  co_return {};
}
*/

/*
auto definition(JsonRpcServer* srv, json const& params) -> Coroutine<json> {
  auto const d = params.at("textDocument").get<TextDocumentIdentifier>();
  auto const p = params.at("position").get<Position>();
  logMessage(
    srv,
    MessageType::log,
    "Query definition at " + d.uri + ", " + std::to_string(p.line) + ":" + std::to_string(p.character)
  );
  auto const& e = docs[d.uri];
  auto const index = toIndex(e, p);
  auto& tokens = e.result.tokens;
  for (const auto& token: tokens)
    if (token.begin <= index && token.end >= index) {
      if (!token.defPos) continue;
      co_return Location{doc.uri, fromIndices(e.doc, token.defPos->first, token.defPos->second)};
    }
  co_return {};
}
*/

auto main() -> int {
  // Windows automatically converts between "\r\n" and "\n" if cin/cout is in "text mode".
  // Change to "binary mode" disables this conversion. There is no standard (platform-independent) way of doing it [1].
  // On Unix systems there is no difference between "text mode" and "binary mode" [2].
  //   [1]: https://stackoverflow.com/questions/7587595/read-binary-data-from-stdcin
  //   [2]:
  //   https://stackoverflow.com/questions/25823310/is-there-any-difference-between-text-and-binary-mode-in-file-access
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
  auto srv = server::JsonRpcServer(std::cin, std::cout /*, log */);

  // The registered functions will be executed in one single thread!
  // So don't do any blocking (e.g. wait, sleep, cin >> s)...
  // Expensive computations (we don't have any yet) should be in separate threads too
  srv.addMethod("initialize", initialize);
  srv.addMethod("test1", test1);
  srv.addNotification("test2", test2);
  srv.addMethod("shutdown", shutdown);
  srv.addNotification("exit", stop);
  srv.addNotification("textDocument/didOpen", didOpenTextDocument);
  srv.addNotification("textDocument/didChange", didChangeTextDocument);
  srv.addNotification("textDocument/didClose", didCloseTextDocument);
  // srv.addMethod("textDocument/hover", hover);
  // srv.addMethod("textDocument/definition", definition);

  // Start the server thread and wait until it was shut down...
  srv.startListen();
  srv.waitForComplete();
  // log << "Server stopped." << std::endl;

  return 0;
}
