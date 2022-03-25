// Server :: LSP

#ifndef LSP_HPP_
#define LSP_HPP_

#include <string>
#include <vector>
#include <optional>
#include <nlohmann/json_fwd.hpp>


namespace Server::LSP {

  using std::string;
  using std::vector;
  using std::optional;


  #define conv(T) \
    struct T; \
    void to_json(nlohmann::json&, const T&); \
    void from_json(const nlohmann::json&, T&); \
    struct T

  #define enumconv(T) \
    enum class T: unsigned int; \
    void to_json(nlohmann::json&, const T&); \
    void from_json(const nlohmann::json&, T&); \
    enum class T: unsigned int

  enum class DiagnosticSeverity: unsigned int { UNKNOWN = 0, ERROR = 1, WARNING = 2, INFORMATION = 3, HINT = 4 };
  enum class DiagnosticTag: unsigned int { UNKNOWN = 0, UNNECESSARY = 1, DEPRECATED = 2 };
  enum class MessageType: unsigned int { UNKNOWN = 0, ERROR = 1, WARNING = 2, INFO = 3, LOG = 4 };
  enumconv(MarkupKind) { PLAINTEXT = 0, MARKDOWN = 1 };

  using DocumentUri = string;
  using URI = string;

  conv(Position) {
    unsigned int line{};
    unsigned int character{};
  };

  conv(Range) {
    Position start{};
    Position end{};
  };

  conv(TextDocumentItem) {
    DocumentUri uri{};
    optional<string> languageId{};
    optional<int> version{};
    optional<string> text{};
  };

  conv(TextDocumentIdentifier) {
    DocumentUri uri{};
  };

  conv(VersionedTextDocumentIdentifier): public TextDocumentIdentifier {
    int version{};
  };

  conv(TextDocumentContentChangeEvent) {
    optional<Range> range{};
    string text{};
  };

  conv(CodeDescription) {
    URI href{};
  };

  conv(Location) {
    DocumentUri uri{};
    Range range{};
  };

  conv(DiagnosticsRelatedInformation) {
    Location location{};
    string message{};
  };

  conv(Diagnostic) {
    Range range{};
    string message{};
    optional<DiagnosticSeverity> severity{};
    optional<int> code{};
    optional<CodeDescription> codeDescription{};
    optional<vector<DiagnosticTag>> tags{};
    optional<vector<DiagnosticsRelatedInformation>> relatedInformation{};
    optional<string> source{};
  };

  conv(MarkupContent) {
    MarkupKind kind{};
    string value{};
  };

  conv(MarkedString) { // Outgoing only?
    string language{};
    string value{};
  };

  #undef conv

}

#endif // LSP_HPP_
