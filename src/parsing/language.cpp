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
    }, false);
    mp[tid] = sym;
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

  Symbol Language::addPatternImpl(const string& name, type_index tid, NFA pattern, bool discard, function<std::any(const string&)> action) {

    // Insert new symbol if not already present
    auto it = mp.find(tid);
    if (it != mp.end()) throw Core::NotImplemented("Language: multiple patterns is not supported");
    Symbol sym = symbols.size();
    symbols.emplace_back("<" + name + ">", [sym, action] (const ParseTree* x) -> std::any {
      if (x->id != sym) throw Core::Unreachable("Language: unexpected symbol");
      if (!x->lexeme.has_value()) throw Core::Unreachable("Language: no matching rule");
      return action(x->lexeme.value_or(""));
    }, discard);
    mp[tid] = sym;

    // Add new pattern
    NFALexer::addPattern(sym, pattern);

    return sym;
  }

  Symbol Language::addRuleImpl(const string& name, Symbol lhs, const vector<Symbol>& rhs, std::function<std::any(const ParseTree*)> action) {

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

    return lhs;
  }

  // TEMP CODE
  ParseTree* Language::parseImpl(const string& str, Symbol start) {

    // Scan (using NFA for debugging speed)
    // DFALexer dfa(*this);
    // dfa.optimize();
    // dfa.setString(str);
    NFALexer::setString(str);

    vector<Token> tokens;
    // auto next = dfa.getNextToken();
    auto next = NFALexer::getNextToken();
    while (next) {
      Token tok = next.value();
      if (!symbols[tok.id].discard) tokens.push_back(tok);
      // next = dfa.getNextToken();
      next = NFALexer::getNextToken();
    }

    // Parse
    this->startSymbol = start;
    ParseTree* x = EarleyParser::parse(tokens, pool);

    return x;
  }

}
