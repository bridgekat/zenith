// Server :: LSP

#ifndef LSP_HPP_
#define LSP_HPP_

#include <cstdint>
#include <optional>
#include <string>
#include <vector>
#include <nlohmann/json_fwd.hpp>

namespace Server::LSP {

  using std::string;
  using std::vector;
  using std::optional;

#define structconv(T)                        \
  struct T;                                  \
  void to_json(nlohmann::json&, const T&);   \
  void from_json(const nlohmann::json&, T&); \
  struct T

#define enumconv(T)                          \
  enum class T : uint32_t;                   \
  void to_json(nlohmann::json&, const T&);   \
  void from_json(const nlohmann::json&, T&); \
  enum class T : uint32_t

  enum class DiagnosticSeverity : uint32_t { UNKNOWN = 0, ERROR = 1, WARNING = 2, INFORMATION = 3, HINT = 4 };
  enum class DiagnosticTag : uint32_t { UNKNOWN = 0, UNNECESSARY = 1, DEPRECATED = 2 };
  enum class MessageType : uint32_t { UNKNOWN = 0, ERROR = 1, WARNING = 2, INFO = 3, LOG = 4 };
  enumconv(MarkupKind){PLAINTEXT = 0, MARKDOWN = 1};

  using DocumentUri = string;
  using URI = string;

  structconv(Position) {
    uint32_t line{};
    uint32_t character{};
  };

  structconv(Range) {
    Position start{};
    Position end{};
  };

  structconv(TextDocumentItem) {
    DocumentUri uri{};
    optional<string> languageId{};
    optional<int32_t> version{};
    optional<string> text{};
  };

  structconv(TextDocumentIdentifier) { DocumentUri uri{}; };

  structconv(VersionedTextDocumentIdentifier): public TextDocumentIdentifier { int32_t version{}; };

  structconv(TextDocumentContentChangeEvent) {
    optional<Range> range{};
    string text{};
  };

  structconv(CodeDescription) { URI href{}; };

  structconv(Location) {
    DocumentUri uri{};
    Range range{};
  };

  structconv(DiagnosticsRelatedInformation) {
    Location location{};
    string message{};
  };

  structconv(Diagnostic) {
    Range range{};
    string message{};
    optional<DiagnosticSeverity> severity{};
    optional<int32_t> code{};
    optional<CodeDescription> codeDescription{};
    optional<vector<DiagnosticTag>> tags{};
    optional<vector<DiagnosticsRelatedInformation>> relatedInformation{};
    optional<string> source{};
  };

  structconv(MarkupContent) {
    MarkupKind kind{};
    string value{};
  };

  structconv(MarkedString) { // Outgoing only?
    string language{};
    string value{};
  };

#undef structconv

}

#endif // LSP_HPP_
