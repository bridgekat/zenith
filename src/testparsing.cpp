#include <utility>
#include <string>
#include <vector>
#include <optional>
#include <iostream>
#include <fstream>
#include <sstream>
#include "core.hpp"
#include "mu.hpp"

using std::pair, std::string, std::vector;
using std::optional, std::make_optional, std::nullopt;
using std::cin, std::cout, std::endl;
using Parsing::Symbol, Parsing::ParseTree;
using Parsing::NFALexer, Parsing::DFALexer, Parsing::EarleyParser;


// See: https://stackoverflow.com/questions/116038/how-do-i-read-an-entire-file-into-a-stdstring-in-c
string readFile(std::ifstream& in) {
  std::ostringstream sstr;
  sstr << in.rdbuf();
  return sstr.str();
}

int main() {

  std::ifstream in("test.mu");
  string content = readFile(in);
  in.close();

  Mu mu;
  mu.analyze(content);

  return 0;
}
