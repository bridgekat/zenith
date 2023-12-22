#include "document.hpp"
#include <codecvt>
#include <locale>

namespace apimu::server {
#include "macros_open.hpp"

  auto cvt = std::wstring_convert<std::codecvt_utf8_utf16<char16_t>, char16_t>(); // NOLINT

  auto Document::toUtf8(Position utf16) const -> Position {
    std::u16string s = cvt.from_bytes(lines.at(utf16.first));
    return {utf16.first, cvt.to_bytes(s.substr(0, utf16.second)).size()};
  }

  auto Document::toUtf16(Position utf8) const -> Position {
    std::string s = lines.at(utf8.first);
    return {utf8.first, cvt.from_bytes(s.substr(0, utf8.second)).size()};
  }

  auto Document::process() -> void {
    // Detect line endings
    auto const cr = content.find('\r') != std::string::npos;
    auto const lf = content.find('\n') != std::string::npos;
    eol = (cr && lf) ? "\r\n" : cr ? "\r" : "\n"; // Default to LF...

    auto const n = content.size();
    lines.clear();
    apos.clear();
    aindex.clear();

    auto lineBreak = std::vector<bool>(n + 1, false);
    for (auto i = 0uz; i <= n; i++) {
      if (content.substr(i, eol.size()) == eol) {
        if (i + eol.size() > n)
          unreachable;
        lineBreak[i + eol.size()] = true;
      }
    }

    auto lastLineIndex = 0uz;
    aindex.emplace_back();
    for (auto i = 0uz; i <= n; i++) {
      if (lineBreak[i]) {
        aindex.back().push_back(i); // Probably not needed
        aindex.emplace_back();
        lines.push_back(content.substr(lastLineIndex, i - lastLineIndex));
        lastLineIndex = i;
      }
      apos.emplace_back(lines.size(), i - lastLineIndex);
      aindex.back().push_back(i);
    }
    lines.push_back(content.substr(lastLineIndex, n - lastLineIndex));
  }

#include "macros_close.hpp"
}
