#ifndef APIMU_SERVER_DOCUMENT_HPP
#define APIMU_SERVER_DOCUMENT_HPP

#include "json_rpc_server.hpp"

namespace apimu::server {
#include "macros_open.hpp"

  // Naive implementation, highly inefficient, but should be enough for current purpose...
  class Document {
  public:
    using Position = std::pair<size_t, size_t>;

    Document() {
      process();
    }

    auto toIndex(Position pos) const -> size_t {
      return aindex.at(pos.first).at(pos.second);
    }
    auto toPosition(size_t index) const -> Position {
      return apos.at(index);
    }
    auto toUtf8(Position utf16) const -> Position;
    auto toUtf16(Position utf8) const -> Position;

    auto eolIndicator() const -> std::string {
      return eol == "\r\n" ? "\\r\\n" : eol == "\r" ? "\\r" : "\\n";
    }
    auto getContent() const -> std::string const& {
      return content;
    }
    auto setContent(std::string const& s) -> void {
      content = s;
      process();
    }
    auto modify(size_t start, size_t end, std::string const& s) -> void {
      content = content.substr(0, start) + s + content.substr(end);
      process();
    }

  private:
    std::string eol, content;
    // States managed by `process()`
    std::vector<std::string> lines;
    std::vector<std::pair<size_t, size_t>> apos;
    std::vector<std::vector<size_t>> aindex;

    void process();
  };

#include "macros_close.hpp"
}

#endif // APIMU_SERVER_DOCUMENT_HPP
