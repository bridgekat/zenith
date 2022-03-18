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
#include "server/languageserver.hpp"
#include "mu.hpp"

using std::cin, std::cout, std::cerr, std::endl;
using std::pair, std::string, std::stringstream, nlohmann::json;
using std::optional, std::make_optional, std::nullopt;
using std::vector;
using Server::Coroutine, Server::JSONRPC2Exception, Server::JSONRPC2Server;
using Server::Document;


#define to(name) j[#name] = o.name
#define opt_to(name) if (o.name) j[#name] = *o.name
#define from(name) j.at(#name).get_to(o.name)
#define opt_from(name) o.name = j.contains(#name) ? make_optional(j[#name].get<decltype(o.name)::value_type>()) : nullopt;

struct Position {
  unsigned int line = 0;
  unsigned int character = 0;
};
void to_json   (json& j, const Position& o) { j = {}; to(line); to(character); }
void from_json (const json& j, Position& o) { o = {}; from(line); from(character); }

struct Range {
  Position start = {};
  Position end = {};
};
void to_json   (json& j, const Range& o) { j = {}; to(start); to(end); }
void from_json (const json& j, Range& o) { o = {}; from(start); from(end); }

typedef string DocumentUri;
typedef string URI;

struct TextDocumentItem {
  DocumentUri uri = "";
  optional<string> languageId = "";
  optional<int> version = -1;
  optional<string> text = "";
};
void to_json   (json& j, const TextDocumentItem& o) { j = {}; to(uri); opt_to(languageId); opt_to(version); opt_to(text); }
void from_json (const json& j, TextDocumentItem& o) { o = {}; from(uri); opt_from(languageId); opt_from(version); opt_from(text); }

struct VersionedTextDocumentIdentifier {
  int version = -1;
};
void to_json   (json& j, const VersionedTextDocumentIdentifier& o) { j = {}; to(version); }
void from_json (const json& j, VersionedTextDocumentIdentifier& o) { o = {}; from(version); }

struct TextDocumentContentChangeEvent {
  optional<Range> range = nullopt;
  string text = "";
};
void to_json   (json& j, const TextDocumentContentChangeEvent& o) { j = {}; opt_to(range); to(text); }
void from_json (const json& j, TextDocumentContentChangeEvent& o) { o = {}; opt_from(range); from(text); }

enum class DiagnosticSeverity: unsigned int { UNKNOWN = 0, ERROR = 1, WARNING = 2, INFORMATION = 3, HINT = 4 };
void to_json   (json& j, const DiagnosticSeverity& o) { j = static_cast<unsigned int>(o); }
void from_json (const json& j, DiagnosticSeverity& o) { o = static_cast<DiagnosticSeverity>(j.get<unsigned int>()); }

enum class DiagnosticTag: unsigned int { UNKNOWN = 0, UNNECESSARY = 1, DEPRECATED = 2 };
void to_json   (json& j, const DiagnosticTag& o) { j = static_cast<unsigned int>(o); }
void from_json (const json& j, DiagnosticTag& o) { o = static_cast<DiagnosticTag>(j.get<unsigned int>()); }

struct CodeDescription {
  URI href = "";
};
void to_json   (json& j, const CodeDescription& o) { j = {}; to(href); }
void from_json (const json& j, CodeDescription& o) { o = {}; from(href); }

struct Location {
  DocumentUri uri = "";
  Range range = {};
};
void to_json   (json& j, const Location& o) { j = {}; to(uri); to(range); }
void from_json (const json& j, Location& o) { o = {}; from(uri); from(range); }

struct DiagnosticRelatedInformation {
  Location location = {};
  string message = "";
};
void to_json   (json& j, const DiagnosticRelatedInformation& o) { j = {}; to(location); to(message); }
void from_json (const json& j, DiagnosticRelatedInformation& o) { o = {}; from(location); from(message); }

struct Diagnostic {
  Range range = {};
  string message = "";
  optional<DiagnosticSeverity> severity = nullopt;
  optional<int> code = nullopt;
  optional<CodeDescription> codeDescription = nullopt;
  optional<vector<DiagnosticTag>> tags = nullopt;
  optional<vector<DiagnosticRelatedInformation>> relatedInformation = nullopt;
  optional<string> source = "Mu analyzer"; // Only server can send these
};
void to_json   (json& j, const Diagnostic& o) { j = {}; to(range); opt_to(severity); opt_to(code); opt_to(codeDescription); opt_to(source); to(message); opt_to(tags); opt_to(relatedInformation); }
void from_json (const json& j, Diagnostic& o) { o = {}; from(range); opt_from(severity); opt_from(code); opt_from(codeDescription); opt_from(source); from(message); opt_from(tags); opt_from(relatedInformation); }

#undef to
#undef opt_to
#undef from
#undef opt_from


std::unordered_map<DocumentUri, Document> docs;

enum class MessageType: unsigned int { UNKNOWN = 0, ERROR = 1, WARNING = 2, INFO = 3, LOG = 4 };

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

Range fromIndices(const Document& doc, size_t start, size_t end) {
  Document::Position s = doc.toUTF16(doc.toPosition(start));
  Document::Position t = doc.toUTF16(doc.toPosition(end));
  Range res;
  res.start.line = s.first;
  res.start.character = s.second;
  res.end.line = t.first;
  res.end.character = t.second;
  return res;
}

void analyzeDocument(JSONRPC2Server* srv, const DocumentUri& uri) {
  const Document& doc = docs[uri];
  string s = doc.getContent();
  vector<Diagnostic> res;

  Mu mu;
  mu.analyze(s);
  for (const auto& ex: mu.popParsingErrors()) {
    res.emplace_back(fromIndices(doc, ex.startPos, ex.endPos), ex.what(), DiagnosticSeverity::WARNING);
  }
  for (const auto& ex: mu.popAnalysisErrors()) {
    res.emplace_back(fromIndices(doc, ex.startPos, ex.endPos), ex.what(), DiagnosticSeverity::ERROR);
  }

  srv->callNotification("textDocument/publishDiagnostics", {
    {"uri", uri},
    {"diagnostics", res}
  });
}


Coroutine<json> initialize(JSONRPC2Server*, const json&) {
  // This is a method.
  // We must send a response to it (`co_return` a json).
  co_return {
    {"capabilities", {
      {"textDocumentSync", {
        {"openClose", true},
        {"change", 2} // None: 0, Full: 1, Incremental: 2
      }},
      // {"hoverProvider", true},
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

Coroutine<void> didOpenTextDocument(JSONRPC2Server* srv, const json& params) {
  auto doc = params.at("textDocument").get<TextDocumentItem>();
  logMessage(srv, MessageType::LOG,
    "Text document opened: " + doc.uri
      + ", lang: " + (doc.languageId? *doc.languageId : "unknown")
      + ", version: " + (doc.version? std::to_string(*doc.version) : "unknown")
      + ", length: " + (doc.text? std::to_string(doc.text->size()) : "unknown"));
  if (doc.text) {
    docs[doc.uri].setContent(*doc.text);
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
  Document& d = docs[doc.uri];
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
// But if you throw other kinds of exceptions, std::terminate() will be called (i.e. the program will crash).


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
  srv.addNotification ("textDocument/didOpen", didOpenTextDocument);
  srv.addNotification ("textDocument/didChange", didChangeTextDocument);
  srv.addNotification ("textDocument/didClose", didCloseTextDocument);
  srv.addMethod       ("shutdown",   shutdown);
  srv.addNotification ("exit",       exit_);

  // Start the server thread and wait until it was shut down...
  srv.startListen();
  srv.waitForComplete();
  log << "Server stopped." << std::endl;

  return 0;
}
