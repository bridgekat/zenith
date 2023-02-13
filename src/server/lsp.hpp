#ifndef APIMU_SERVER_LSP_HPP
#define APIMU_SERVER_LSP_HPP

#include <cstdint>
#include <optional>
#include <string>
#include <vector>
#include <nlohmann/json_fwd.hpp>

namespace apimu::server::lsp {

#define STRUCT_CONV(T)                       \
  struct T;                                  \
  void to_json(nlohmann::json&, T const&);   \
  void from_json(nlohmann::json const&, T&); \
  struct T

#define ENUM_CONV(T)                         \
  enum class T : std::uint32_t;              \
  void to_json(nlohmann::json&, T const&);   \
  void from_json(nlohmann::json const&, T&); \
  enum class T : std::uint32_t

  enum class DiagnosticSeverity : std::uint32_t { unknown = 0, error, warning, information, hint };
  enum class DiagnosticTag : std::uint32_t { unknown = 0, unnecessary, deprecated };
  enum class MessageType : std::uint32_t { unknown = 0, error, warning, info, log };
  ENUM_CONV(MarkupKind){plaintext = 0, markdown};

  using DocumentUri = std::string;
  using Uri = std::string;

  STRUCT_CONV(Position) {
    std::uint32_t line = 0;
    std::uint32_t character = 0;
  };

  STRUCT_CONV(Range) {
    Position start;
    Position end;
  };

  STRUCT_CONV(TextDocumentItem) {
    DocumentUri uri;
    std::optional<std::string> languageId;
    std::optional<std::int32_t> version;
    std::optional<std::string> text;
  };

  STRUCT_CONV(TextDocumentIdentifier) { DocumentUri uri; };

  STRUCT_CONV(VersionedTextDocumentIdentifier):
    TextDocumentIdentifier {
    std::int32_t version = 0;
  };

  STRUCT_CONV(TextDocumentContentChangeEvent) {
    std::optional<Range> range;
    std::string text;
  };

  STRUCT_CONV(CodeDescription) { Uri href; };

  STRUCT_CONV(Location) {
    DocumentUri uri;
    Range range;
  };

  STRUCT_CONV(DiagnosticsRelatedInformation) {
    Location location;
    std::string message;
  };

  STRUCT_CONV(Diagnostic) {
    Range range;
    std::string message;
    std::optional<DiagnosticSeverity> severity;
    std::optional<std::int32_t> code = {};
    std::optional<CodeDescription> codeDescription = {};
    std::optional<std::vector<DiagnosticTag>> tags = {};
    std::optional<std::vector<DiagnosticsRelatedInformation>> relatedInformation = {};
    std::optional<std::string> source = {};
  };

  STRUCT_CONV(MarkupContent) {
    MarkupKind kind;
    std::string value;
  };

  STRUCT_CONV(MarkedString) { // Outgoing only?
    std::string language;
    std::string value;
  };

#undef STRUCT_CONV
#undef ENUM_CONV
}

#endif // APIMU_SERVER_LSP_HPP
