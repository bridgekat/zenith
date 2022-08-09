#include "lsp.hpp"
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wdeprecated"
#include <nlohmann/json.hpp>
#pragma GCC diagnostic pop

namespace Server::LSP {

  using nlohmann::json;

// Adapted from nlohmann::json `nlohmann/detail/macroscope.hpp`
#define from_to_simple(Type, ...)                                              \
  void to_json(json& nlohmann_json_j, const Type& nlohmann_json_t) {           \
    NLOHMANN_JSON_EXPAND(NLOHMANN_JSON_PASTE(NLOHMANN_JSON_TO, __VA_ARGS__))   \
  }                                                                            \
  void from_json(const json& nlohmann_json_j, Type& nlohmann_json_t) {         \
    NLOHMANN_JSON_EXPAND(NLOHMANN_JSON_PASTE(NLOHMANN_JSON_FROM, __VA_ARGS__)) \
  }

// Adapted from nlohmann::json `nlohmann/detail/macroscope.hpp`
#define from_to_enum(EnumType, ...)                                                                             \
  void to_json(json& j, const EnumType& e) {                                                                    \
    static_assert(std::is_enum<EnumType>::value, #EnumType " must be an enum!");                                \
    static const std::pair<EnumType, json> m[] = __VA_ARGS__;                                                   \
    auto it = std::find_if(std::begin(m), std::end(m), [e](const std::pair<EnumType, json>& ej_pair) -> bool {  \
      return ej_pair.first == e;                                                                                \
    });                                                                                                         \
    j = ((it != std::end(m)) ? it : std::begin(m))->second;                                                     \
  }                                                                                                             \
  void from_json(const json& j, EnumType& e) {                                                                  \
    static_assert(std::is_enum<EnumType>::value, #EnumType " must be an enum!");                                \
    static const std::pair<EnumType, json> m[] = __VA_ARGS__;                                                   \
    auto it = std::find_if(std::begin(m), std::end(m), [&j](const std::pair<EnumType, json>& ej_pair) -> bool { \
      return ej_pair.second == j;                                                                               \
    });                                                                                                         \
    e = ((it != std::end(m)) ? it : std::begin(m))->first;                                                      \
  }

  // clang-format off
#define to(name) j[#name] = o.name
#define opt_to(name) if (o.name) j[#name] = *o.name
#define from(name) j.at(#name).get_to(o.name)
#define opt_from(name) o.name = j.contains(#name) ? std::make_optional(j[#name].get<decltype(o.name)::value_type>()) : std::nullopt;

  from_to_enum(MarkupKind, { {MarkupKind::PLAINTEXT, "plaintext"}, {MarkupKind::MARKDOWN, "markdown"} });
  from_to_simple(Position, line, character);
  from_to_simple(Range, start, end);
  void to_json   (json& j, const TextDocumentItem& o) { j = {}; to(uri); opt_to(languageId); opt_to(version); opt_to(text); }
  void from_json (const json& j, TextDocumentItem& o) { o = {}; from(uri); opt_from(languageId); opt_from(version); opt_from(text); }
  from_to_simple(TextDocumentIdentifier, uri);
  from_to_simple(VersionedTextDocumentIdentifier, uri, version);
  void to_json   (json& j, const TextDocumentContentChangeEvent& o) { j = {}; opt_to(range); to(text); }
  void from_json (const json& j, TextDocumentContentChangeEvent& o) { o = {}; opt_from(range); from(text); }
  from_to_simple(CodeDescription, href);
  from_to_simple(Location, uri, range);
  from_to_simple(DiagnosticsRelatedInformation, location, message);
  void to_json   (json& j, const Diagnostic& o) { j = {}; to(range); to(message); opt_to(severity); opt_to(code); opt_to(codeDescription); opt_to(tags); opt_to(relatedInformation); opt_to(source); }
  void from_json (const json& j, Diagnostic& o) { o = {}; from(range); from(message); opt_from(severity); opt_from(code); opt_from(codeDescription); opt_from(tags); opt_from(relatedInformation); opt_from(source); }
  from_to_simple(MarkupContent, kind, value);
  from_to_simple(MarkedString, language, value);

  // clang-format on
#undef from_to_simple
#undef from_to_enum
#undef to
#undef opt_to
#undef from
#undef opt_from

}
