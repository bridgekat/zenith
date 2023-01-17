// Server :: Document, LanguageServer

#ifndef LANGUAGE_SERVER_HPP_
#define LANGUAGE_SERVER_HPP_

#include "jsonrpc2.hpp"

namespace Server {

  // Naive implementation, highly inefficient, but should be enough for current purpose...
  class Document {
  public:
    using Position = std::pair<size_t, size_t>;

    Document():
      eol(),
      content(),
      lines(),
      apos(),
      aindex() {
      process();
    }

    size_t toIndex(const Position& pos) const { return aindex.at(pos.first).at(pos.second); }
    Position toPosition(size_t index) const { return apos.at(index); }
    Position toUTF8(const Position& utf16) const;
    Position toUTF16(const Position& utf8) const;

    string eolIndicator() const { return eol == "\r\n" ? "\\r\\n" : eol == "\r" ? "\\r" : "\\n"; }
    const string& getContent() const { return content; }
    void setContent(const string& s) {
      content = s;
      process();
    }
    void modify(size_t start, size_t end, const string& s) {
      content = content.substr(0, start) + s + content.substr(end);
      process();
    }

  private:
    string eol, content;
    // States managed by `process()`
    std::vector<string> lines;
    std::vector<std::pair<size_t, size_t>> apos;
    std::vector<std::vector<size_t>> aindex;

    void process();
  };

}

#endif // LANGUAGE_SERVER_HPP_
