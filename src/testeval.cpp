#include <fstream>
#include <iostream>
#include <span>
#include <sstream>
#include <string>
#include <vector>
#include <core/expr.hpp>
#include <core/fol/fol.hpp>
#include <eval/extended_evaluator.hpp>
#include <eval/tree.hpp>

using std::string;
using std::cin, std::cout, std::endl;
using namespace apimu;

// See: https://stackoverflow.com/questions/116038/how-do-i-read-an-entire-file-into-a-stdstring-in-c
auto readFile(std::ifstream&& in) -> string {
  std::ostringstream sstr;
  sstr << in.rdbuf();
  return sstr.str();
}

auto main(int argc, char* argv[]) -> int {
  auto const args = std::span(argv, static_cast<size_t>(argc));
  auto evaluator = eval::ExtendedEvaluator();
  auto in = string();
  for (auto i = 1_z; i < args.size(); i++) in += readFile(std::ifstream(args[i])) + "\n";

  while (true) {
    if (in.empty()) {
      cout << ">> ";
      std::getline(cin, in);
    }
    if (in.starts_with(':')) {
      in = in.substr(1);
      /* if (in.starts_with("reset")) { // Reset state
        in = in.substr(5);
        evaluator.reset();
      } else */
      if (in.starts_with('{')) { // Multi-line input
        in = in.substr(1) + "\n";
        string curr;
        std::getline(cin, curr);
        while (curr != ":}") {
          in += curr + "\n";
          std::getline(cin, curr);
        }
      } else if (in.starts_with("load")) { // Load file
        in = in.substr(4);
        while (in.starts_with(' ')) in = in.substr(1);
        in = readFile(std::ifstream(in));
      } else if (in.starts_with("quit")) {
        break;
      }
    }
    evaluator.setString(in);
    while (true) {
      auto const more = evaluator.parseNextStatement();
      auto const& err = evaluator.parsingErrors();
      for (auto const& ex: err) {
        cout << endl;
        cout << "× " << ex.what() << endl;
        cout << "| " << endl;
        cout << "| " << in << endl;
        cout << "| " << std::string(ex.begin, ' ') << std::string(ex.end - ex.begin, '~') << endl;
        cout << endl;
      }
      if (!more || !err.empty()) break;
      try {
        auto const& res = evaluator.evalParsedStatement();
        cout << res->toString() << endl;
      } catch (eval::EvalError& ex) {
        auto const& [found, prefix] = ex.e->toStringUntil(ex.at);
        cout << endl;
        if (found) {
          cout << "× Error evaluating, " << ex.what() << endl;
          cout << "| " << endl;
          cout << "| " << ex.e->toString() << endl;
          cout << "| " << std::string(prefix.size(), ' ') << std::string(ex.at->toString().size(), '~') << endl;
        } else {
          cout << "× Error evaluating, " << ex.what() << endl;
          cout << "  At: " << ex.at->toString() << endl;
          cout << "  In: " << ex.e->toString() << endl;
        }
        cout << endl;
      }
    }
    in.clear();
  }

  return 0;
}
