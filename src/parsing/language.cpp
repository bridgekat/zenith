#include "language.hpp"


namespace Parsing {

  using std::type_index;
  using std::any;
  using std::function;


  vector<Language::ParsingErrorException> Language::popParsingErrors() {
    vector<ParsingErrorException> res;
    // See: https://stackoverflow.com/questions/30448182/is-it-safe-to-use-a-c11-range-based-for-loop-with-an-rvalue-range-init
    for (const auto& e: lexer.popErrors()) {
      res.emplace_back(e.startPos, e.endPos, "Parsing error, unexpected characters: " + e.lexeme);
    }
    for (const auto& e: parser.popErrors()) {
      string s = "Parsing error, expected one of:\n";
      bool first = true;
      for (Symbol sym: e.expected) {
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
      res.emplace_back(e.startPos, e.endPos, s);
    }
    for (const auto& e: parser.popAmbiguities()) {
      string s = "Warning: unresolved ambiguity\n";
      s += "(Alternative parse tree display has not been implemented yet;"
           " you can try adding commas and parentheses or modifying notations to eliminate ambiguity."
           " If you cannot get rid of this message, it is likely that the base grammar is incorrect;"
           " you may submit an issue on GitHub.)";
      res.emplace_back(e.startPos, e.endPos, s);
    }
    return res;
  }

  Symbol Language::getSymbol(type_index tid) {
    auto it = mp.find(tid);
    if (it != mp.end()) return it->second;
    Symbol sym = newSymbol();
    mp[tid] = sym;
    return sym;
  }

  Symbol Language::newSymbol(const string& name) {
    Symbol sym = symbols.size();
    // symbols.emplace_back(...)
    symbols.push_back(Entry{ name, [sym] (const ParseTree* x) -> std::any {
      if (x->id != sym) throw Core::Unreachable("Language: unexpected symbol");
      throw Core::Unreachable("Language: no matching rule or pattern");
    }});
    return sym;
  }

  void Language::setAsIgnoredSymbol(const string& name, Symbol sym) {
    if (parser.ignoredSymbol) throw Core::Unreachable("Language: at most one ignored symbol can be set");
    parser.ignoredSymbol = sym;
    symbols[sym].name = name;
  }

  size_t Language::addPatternImpl(const string& name, Symbol sym, NFALexer::NFA pattern, std::function<std::any(const ParseTree*)> action) {
    // Update name
    symbols[sym].name = "<" + name + ">";
    // Add new pattern
    size_t pid = lexer.addPattern(sym, pattern);
    // Add new handler for new pattern
    auto prev = symbols[sym].action;
    symbols[sym].action = [sym, pid, prev, action] (const ParseTree* x) -> std::any {
      if (x->id != sym) throw Core::Unreachable("Language: unexpected symbol");
      if (x->patternIndex.has_value() && x->patternIndex.value() == pid) return action(x);
      return prev(x);
    };
    return pid;
  }

  size_t Language::addRuleImpl(const string& name, Symbol lhs, const vector<Symbol>& rhs, std::function<std::any(const ParseTree*)> action, size_t prec) {
    // Update name
    symbols[lhs].name = "[" + name + "]";
    // Add new production rule
    size_t rid = parser.rules.size();
    // parser.rules.emplace_back(lhs, rhs, prec);
    parser.rules.push_back(Rule{ lhs, rhs, prec });
    // Add new handler for new rule
    auto prev = symbols[lhs].action;
    symbols[lhs].action = [lhs, rid, prev, action] (const ParseTree* x) -> std::any {
      if (x->id != lhs) throw Core::Unreachable("Language: unexpected symbol");
      if (x->ruleIndex.has_value() && x->ruleIndex.value() == rid) return action(x);
      return prev(x);
    };
    return rid;
  }

  ParseTree* Language::nextSentenceImpl(Symbol start) {
    parser.startSymbol = start;
    return parser.nextSentence(pool);
  }

}
