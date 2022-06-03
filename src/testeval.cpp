#include <iostream>
#include <string>
#include <vector>
#include <fstream>
#include <sstream>
#include "core.hpp"
#include "eval/tree.hpp"
#include "eval/evaluator.hpp"

using std::string;
using std::vector;
using std::cin, std::cout, std::endl;
using Core::Allocator;
using Eval::Evaluator, Eval::EvalError;

// See: https://stackoverflow.com/questions/116038/how-do-i-read-an-entire-file-into-a-stdstring-in-c
string readFile(std::ifstream&& in) {
  std::ostringstream sstr;
  sstr << in.rdbuf();
  return sstr.str();
}

int main() {
  Evaluator evaluator;

  while (true) {
    string in;
    cout << ">> ";
    std::getline(cin, in);
    if (in.starts_with(':')) {
      in = in.substr(1);
      /* if (in.starts_with("reset")) { // Reset state
        in = in.substr(5);
        evaluator.reset();
      } else */ if (in.starts_with('{')) { // Multi-line input
        in = in.substr(1);
        string curr;
        std::getline(cin, curr);
        while (curr != ":}") {
          in += curr;
          std::getline(cin, curr);
        }
      } else if (in.starts_with("load")) { // Load file
        in = in.substr(4);
        while (in.starts_with(' ')) in = in.substr(1);
        in = readFile(std::ifstream(in));
      }
    }
    evaluator.setString(in);
    while (true) {
      const auto res = evaluator.evalNextStatement();
      const auto& err = evaluator.popParsingErrors();
      if (!err.empty()) {
        const auto& ex = err[0];
        cout << endl;
        cout << "× " << ex.what() << endl;
        cout << "| " << endl;
        cout << "| " << in << endl;
        cout << "| " << std::string(ex.startPos, ' ')
                     << std::string(ex.endPos - ex.startPos, '~') << endl;
        cout << endl;
        break;
      }
      if (!res) break;
      cout << res->toString() << endl;
    }
  }

  return 0;
}
