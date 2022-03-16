#include "language.hpp"
#include <iostream> // TEMP CODE


namespace Parsing {

  using std::type_index;
  using std::any;
  using std::function;
  using std::cout, std::endl;


  Symbol Language::addPatternImpl(const string& name, type_index tid, NFA pattern, bool discard, function<std::any(const string&)> action) {

    // Insert new symbol if not already present
    auto it = mp.find(tid);
    Symbol sym;
    if (it != mp.end()) throw Core::NotImplemented("Language: multiple patterns is not supported");
    else {
      sym = symbols.size();
      symbols.emplace_back("<" + name + ">", [sym, action] (const ParseTree* x) -> std::any {
        if (x->id != sym) throw Core::Unreachable("Language: unexpected symbol");
        if (!x->lexeme.has_value()) throw Core::Unreachable("Language: no matching rule");
        return action(x->lexeme.value_or(""));
      }, discard);
      it = mp.insert({ tid, sym }).first;
    }

    // Add new pattern
    NFALexer::addPattern(sym, pattern);

    return sym;
  }

  Symbol Language::addRuleImpl(const string& name, type_index tid, const vector<type_index>& rhstid, function<std::any(const vector<std::any>&)> action) {

    // Insert new symbol if not already present
    auto it = mp.find(tid);
    Symbol sym;
    if (it != mp.end()) sym = it->second;
    else {
      sym = symbols.size();
      symbols.emplace_back("", [sym] (const ParseTree* x) -> std::any {
        if (x->id != sym) throw Core::Unreachable("Language: unexpected symbol");
        throw Core::Unreachable("Language: no matching rule");
      }, false);
      it = mp.insert({ tid, sym }).first;
    }

    // Insert new symbols for RHS
    vector<Symbol> rhs;
    for (type_index tid: rhstid) {
      auto it = mp.find(tid);
      Symbol sym;
      if (it != mp.end()) sym = it->second;
      else {
        sym = symbols.size();
        symbols.emplace_back("", [sym] (const ParseTree* x) -> std::any {
          if (x->id != sym) throw Core::Unreachable("Language: unexpected symbol");
          throw Core::Unreachable("Language: no matching rule");
        }, false);
        it = mp.insert({ tid, sym }).first;
      }
      rhs.push_back(sym);
    }

    // Update name
    symbols[sym].name = "[" + name + "]";

    // Add new production rule
    size_t rid = rules.size();
    rules.emplace_back(sym, rhs);

    // Add new handler for new rule
    auto prev = symbols[sym].action;
    symbols[sym].action = [this, sym, rid, prev, action] (const ParseTree* x) -> std::any {
      if (x->id != sym) throw Core::Unreachable("Language: unexpected symbol");
      if (x->ruleIndex.has_value() && x->ruleIndex.value() == rid) {
        vector<std::any> params;
        for (ParseTree* p = x->c; p; p = p->s) {
          params.push_back(symbols[p->id].action(p));
        }
        return action(params);
      }
      return prev(x);
    };

    return sym;
  }

  ParseTree* Language::parseImpl(const string& str, Symbol start) {

    // Avoid cutting UTF-8 segments
    auto cutoff = [] (const string& s, size_t pos) {
      for (; pos < s.size(); pos++) {
        unsigned char c = s[pos];
        if ((c & 0b11000000) != 0b10000000) break;
      }
      return pos;
    };

    // Scan
    DFALexer dfa(*this);
    dfa.optimize();
    dfa.setRest(str);

    vector<Token> tokens;
    while (!dfa.eof()) {
      auto next = dfa.getNextToken();
      if (!next) {
        std::cout << "Parse error at: "
                  << dfa.getRest().substr(0, cutoff(dfa.getRest(), 20))
                  << "...: no prefix matches known patterns "
                      "(most probably due to unsupported ASCII character combinations. "
                      "Is file encoded in UTF-8 and your syntax correct?)" << std::endl;
        dfa.ignoreNextCodepoint();
      } else {
        Token tok = next.value();
        if (!symbols[tok.id].discard) tokens.push_back(tok);
      }
    }

    // Parse
    Core::Allocator<ParseTree> pool;
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
      for (size_t i = 0; i < dpa.size(); i++) {
        if (i > 0 && dpa[i].empty()) {
          string rest = str.substr(toCharsStart(i));
          std::cout << "Parse error at: "
                    << rest.substr(0, cutoff(rest, 20))
                    << "...: no possible parse tree candidates. Expected either one of: ";
          bool first = true;
          for (const auto& ls: dpa[i - 1]) {
            const auto& s = ls.state;
            const Rule& rule = rules[s.ruleIndex];
            if (s.rulePos < rule.rhs.size()) {
              std::cout << (first? "" : ", ") << symbols[rule.rhs[s.rulePos]].name << " (" << rule.rhs[s.rulePos] << ")";
              first = false;
            }
          }
          std::cout << "; got " << symbols[tokens[i].id].name << " (" << tokens[i].id << ")" << std::endl;
          break;
        }
      }
      throw Core::NotImplemented("Language: parsing failed");
    }

    // Get result
    if (x->id != start) throw Core::Unreachable("Language: parsing completed with unexpected root node");

    return x;
  }

}
