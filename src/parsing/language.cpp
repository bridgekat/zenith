#include "language.hpp"


namespace Parsing {

  using std::type_index;
  using std::any;
  using std::function;


  vector<Language::ParsingErrorException> Language::popParsingErrors() {
    vector<ParsingErrorException> res;
    // See: https://stackoverflow.com/questions/30448182/is-it-safe-to-use-a-c11-range-based-for-loop-with-an-rvalue-range-init
    for (const auto& e: NFALexer::popErrors()) {
      res.emplace_back(e.startPos, e.endPos, "Parsing error, unexpected characters: " + e.lexeme);
    }
    for (const auto& e: EarleyParser::popErrors()) {
      string s = "Parsing error, expected one of:\n";
      bool first = true;
      for (Symbol sym: e.expected) if (sym != errorSymbol) {
        string name = symbols.at(sym).name;
        if (name.empty()) name = "(" + std::to_string(sym) + ")";
        s += (first? "" : ", ") + name;
        first = false;
      }
      s += "\n";
      if (e.got) {
        string name = symbols.at(*e.got).name;
        if (name.empty()) name = "(" + std::to_string(*e.got) + ")";
        s += "got token " + name;
      } else {
        s += "but reached the end of file";
      }
      res.emplace_back(e.startPos, e.endPos, s + "\n");
    }
    for (const auto& e: EarleyParser::popAmbiguities()) {
      string s = "Warning, ambiguity detected\n";
      s += "(Alternative parse tree display has not been implemented yet;"
           " you can try to add commas or parentheses to eliminate ambiguity."
           " If you cannot get rid of this message, it is likely that the grammar is incorrect;"
           " please contact zhanrong.qiao21@imperial.ac.uk for this issue.)";
      res.emplace_back(e.startPos, e.endPos, s);
    }
    return res;
  }

  Symbol Language::getSymbol(type_index tid) {
    auto it = mp.find(tid);
    if (it != mp.end()) return it->second;
    Symbol sym = symbols.size();
    symbols.emplace_back("", [sym] (const ParseTree* x) -> std::any {
      if (x->id != sym) throw Core::Unreachable("Language: unexpected symbol");
      throw Core::Unreachable("Language: no matching rule");
    });
    mp[tid] = sym;
    return sym;
  }

  Symbol Language::newSymbol(const string& name, std::function<std::any(const ParseTree*)> action) {
    Symbol sym = symbols.size();
    symbols.emplace_back(name, action);
    return sym;
  }

  void Language::setAsErrorSymbol(const string& name, Symbol sym, std::any val) {
    if (errorSymbol) throw Core::Unreachable("Language: at most one error symbol can be set");
    errorSymbol = sym;
    symbols[sym].name = name;
    symbols[sym].action = [sym, val] (const ParseTree* x) -> std::any {
      if (x->id != sym) throw Core::Unreachable("Language: unexpected symbol");
      return val;
    };
  }

  void Language::setAsIgnoredSymbol(const string& name, Symbol sym) {
    if (ignoredSymbol) throw Core::Unreachable("Language: at most one ignored symbol can be set");
    ignoredSymbol = sym;
    symbols[sym].name = name;
  }

  Symbol Language::setPatternImpl(const string& name, Symbol sym, NFA pattern, std::function<std::any(const ParseTree*)> action) {

    // Update name
    symbols[sym].name = "<" + name + ">";

    // Add new pattern
    NFALexer::addPattern(sym, pattern);

    // Add new handler for new pattern (this will override old patterns, but not old production rules)
    auto prev = symbols[sym].action;
    symbols[sym].action = [sym, prev, action] (const ParseTree* x) -> std::any {
      if (x->id != sym) throw Core::Unreachable("Language: unexpected symbol");
      if (x->lexeme.has_value()) return action(x);
      return prev(x);
    };

    return sym;
  }

  size_t Language::addRuleImpl(const string& name, Symbol lhs, const vector<Symbol>& rhs, std::function<std::any(const ParseTree*)> action) {

    // Update name
    symbols[lhs].name = "[" + name + "]";

    // Add new production rule
    size_t rid = rules.size();
    rules.emplace_back(lhs, rhs);

    // Add new handler for new rule
    auto prev = symbols[lhs].action;
    symbols[lhs].action = [lhs, rid, prev, action] (const ParseTree* x) -> std::any {
      if (x->id != lhs) throw Core::Unreachable("Language: unexpected symbol");
      if (x->ruleIndex.has_value() && x->ruleIndex.value() == rid) return action(x);
      return prev(x);
    };

    return rid;
  }

  // TEMP CODE
  ParseTree* Language::parseImpl(const string& str, Symbol start) {

    this->startSymbol = start;
    NFALexer::setString(str);
    ParseTree* x = EarleyParser::parse(pool);

    return x;
  }

}
