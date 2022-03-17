#include "language.hpp"


namespace Parsing {

  using std::type_index;
  using std::any;
  using std::function;


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

  Symbol Language::addRuleImpl(const string& name, std::type_index tid, const vector<std::type_index>& rhstid, std::function<std::any(const ParseTree*)> action) {

    // Insert new symbol if not already present
    Symbol lhs = getSymbol(tid);
    vector<Symbol> rhs;
    for (type_index tid: rhstid) rhs.push_back(getSymbol(tid));

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
    // dfa.setRest(str);
    NFALexer::setRest(str);

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
    this->start = start;
    ParseTree* x = EarleyParser::parse(tokens, pool);

    /*
    using std::cout, std::endl;
    using LinkedState = EarleyParser::LinkedState;
    if (dpa.size() != tokens.size() + 1) throw Core::Unreachable();

    vector<string> names;
    for (const auto& e: symbols) names.push_back(e.name);
    for (size_t pos = 0; pos <= tokens.size(); pos++) {
      cout << "States at position " << pos << ":" << endl;
      for (const LinkedState& ls: dpa[pos]) {
        cout << showState(ls.state, names) << endl;
      }
      cout << endl;
      if (pos < tokens.size()) cout << "Next token: " << names[tokens[pos].id] << endl;
    }
    */

    if (!x) {
      for (size_t i = 0; i < tokens.size(); i++) {
        if (dpa[i + 1].empty()) {
          string msg = "no possible parse tree candidates. Expected either one of: ";
          bool first = true;
          for (const auto& ls: dpa[i]) {
            const auto& s = ls.state;
            const Rule& rule = rules[s.ruleIndex];
            if (s.rulePos < rule.rhs.size()) {
              msg += (first? "" : ", ") + symbols[rule.rhs[s.rulePos]].name + " (" + std::to_string(rule.rhs[s.rulePos]) + ")";
              first = false;
            }
          }
          msg += "; got " + symbols[tokens[i].id].name + " (" + std::to_string(tokens[i].id) + ")";
          throw ParseErrorException(toCharsStart(i), toCharsEnd(i), "Parsing failed: " + msg);
        }
      }
      throw ParseErrorException(str.size(), str.size(), "Parsing failed, unexpected EOF");
    }

    // Get result
    if (x->id != start) throw Core::Unreachable("Language: parsing completed with unexpected root node");

    return x;
  }

}
