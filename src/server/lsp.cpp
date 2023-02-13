#include "lsp.hpp"
#include <tuple>
#include <nlohmann/json.hpp>

using nlohmann::json;

namespace apimu::server::lsp {

#define FROM_TO_SIMPLE(T, ...)                                                 \
  void to_json(json& nlohmann_json_j, T const& nlohmann_json_t) {              \
    NLOHMANN_JSON_EXPAND(NLOHMANN_JSON_PASTE(NLOHMANN_JSON_TO, __VA_ARGS__))   \
  }                                                                            \
  void from_json(json const& nlohmann_json_j, T& nlohmann_json_t) {            \
    NLOHMANN_JSON_EXPAND(NLOHMANN_JSON_PASTE(NLOHMANN_JSON_FROM, __VA_ARGS__)) \
  }
#define FROM_TO_ENUM(T, ...)                                                                                         \
  void to_json(json& j, T const& e) {                                                                                \
    static_assert(std::is_enum<T>::value, #T " must be an enum!");                                                   \
    static const auto m = std::vector<std::pair<T, json>>(__VA_ARGS__);                                              \
    auto it =                                                                                                        \
      std::find_if(std::begin(m), std::end(m), [e](std::pair<T, json> const& p) -> bool { return p.first == e; });   \
    j = (it != std::end(m) ? it : std::begin(m))->second;                                                            \
  }                                                                                                                  \
  void from_json(json const& j, T& e) {                                                                              \
    static_assert(std::is_enum<T>::value, #T " must be an enum!");                                                   \
    static const auto m = std::vector<std::pair<T, json>>(__VA_ARGS__);                                              \
    auto it =                                                                                                        \
      std::find_if(std::begin(m), std::end(m), [&j](std::pair<T, json> const& p) -> bool { return p.second == j; }); \
    e = (it != std::end(m) ? it : std::begin(m))->first;                                                             \
  }

  // clang-format off
#define TO(name) j[#name] = o.name
#define OPT_TO(name) if (o.name) j[#name] = *o.name
#define FROM(name) j.at(#name).get_to(o.name)
#define OPT_FROM(name) o.name = j.contains(#name) ? std::make_optional(j[#name].get<decltype(o.name)::value_type>()) : std::nullopt;

  FROM_TO_ENUM(MarkupKind, { {MarkupKind::plaintext, "plaintext"}, {MarkupKind::markdown, "markdown"} });
  FROM_TO_SIMPLE(Position, line, character);
  FROM_TO_SIMPLE(Range, start, end);
  void to_json   (json& j, TextDocumentItem const& o) { j = {}; TO(uri); OPT_TO(languageId); OPT_TO(version); OPT_TO(text); }
  void from_json (json const& j, TextDocumentItem& o) { o = {}; FROM(uri); OPT_FROM(languageId); OPT_FROM(version); OPT_FROM(text); }
  FROM_TO_SIMPLE(TextDocumentIdentifier, uri);
  FROM_TO_SIMPLE(VersionedTextDocumentIdentifier, uri, version);
  void to_json   (json& j, TextDocumentContentChangeEvent const& o) { j = {}; OPT_TO(range); TO(text); }
  void from_json (json const& j, TextDocumentContentChangeEvent& o) { o = {}; OPT_FROM(range); FROM(text); }
  FROM_TO_SIMPLE(CodeDescription, href);
  FROM_TO_SIMPLE(Location, uri, range);
  FROM_TO_SIMPLE(DiagnosticsRelatedInformation, location, message);
  void to_json   (json& j, Diagnostic const& o) { j = {}; TO(range); TO(message); OPT_TO(severity); OPT_TO(code); OPT_TO(codeDescription); OPT_TO(tags); OPT_TO(relatedInformation); OPT_TO(source); }
  void from_json (json const& j, Diagnostic& o) { o = {}; FROM(range); FROM(message); OPT_FROM(severity); OPT_FROM(code); OPT_FROM(codeDescription); OPT_FROM(tags); OPT_FROM(relatedInformation); OPT_FROM(source); }
  FROM_TO_SIMPLE(MarkupContent, kind, value);
  FROM_TO_SIMPLE(MarkedString, language, value);

  // clang-format on
#undef FROM_TO_SIMPLE
#undef FROM_TO_ENUM
#undef TO
#undef OPT_TO
#undef FROM
#undef OPT_FROM
}
