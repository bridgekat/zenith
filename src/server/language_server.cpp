#include "language_server.hpp"
#include <codecvt>
#include <locale>

namespace Server {

  std::wstring_convert<std::codecvt_utf8_utf16<char16_t>, char16_t> cvt;

  Document::Position Document::toUTF8(const Position& utf16) const {
    std::u16string s = cvt.from_bytes(lines.at(utf16.first));
    return {utf16.first, cvt.to_bytes(s.substr(0, utf16.second)).size()};
  }

  Document::Position Document::toUTF16(const Position& utf8) const {
    std::string s = lines.at(utf8.first);
    return {utf8.first, cvt.from_bytes(s.substr(0, utf8.second)).size()};
  }

  void Document::process() {
    // Detect line endings
    bool cr = content.find('\r') != string::npos;
    bool lf = content.find('\n') != string::npos;
    eol = (cr && lf) ? "\r\n" : cr ? "\r" : "\n"; // Default to LF...

    size_t n = content.size();
    lines.clear();
    apos.clear();
    aindex.clear();

    std::vector<bool> lineBreak(n + 1, false);
    for (size_t i = 0; i <= n; i++) {
      if (content.substr(i, eol.size()) == eol) {
        if (i + eol.size() > n) unreachable;
        lineBreak[i + eol.size()] = true;
      }
    }

    size_t lastLineIndex = 0;
    aindex.emplace_back();
    for (size_t i = 0; i <= n; i++) {
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

}
