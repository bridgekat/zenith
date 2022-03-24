#include "mu.hpp"
#include <optional>
#include <variant>
#include <iostream>

using std::string;
using std::vector;
using std::pair, std::make_pair;
using std::optional, std::make_optional, std::nullopt;
using std::variant, std::get, std::holds_alternative;
using Parsing::SymbolName, Parsing::Symbol, Parsing::ParseTree, Parsing::makePrec;


// ===================
// Symbol declarations
// ===================

string toLowercaseDashes(const string& s) {
  string res;
  bool first = true;
  for (char c: s) {
    if (c >= 'A' && c <= 'Z') {
      if (!first) res += '-';
      res += (c - 'A' + 'a');
    } else {
      res += c;
    }
    first = false;
  }
  return res;
}

#define symbol(T) \
  struct T; \
  template <> struct Parsing::SymbolName<T> { \
    static const string get() { return toLowercaseDashes(#T); } \
  }; \
  struct T

// Terminal symbols

symbol(Blank) {};
symbol(LineComment) {};
symbol(BlockComment) {};

symbol(Natural) { uint32_t data; };
symbol(String) { string data; };

symbol(OpComma) {};
symbol(OpSemicolon) {};
symbol(OpLParen) {};
symbol(OpRParen) {};
symbol(OpLBrace) {};
symbol(OpRBrace) {};
symbol(OpRRArrow) {};
symbol(OpSlash) {};
symbol(OpVertBar) {};
symbol(OpColonEq) {};

symbol(Identifier) { string name; };

// Nonterminal symbols

symbol(KwAny) {};
symbol(KwAnyFunc) {};
symbol(KwAnyPred) {};
symbol(KwAssume) {};
symbol(KwName) {};
symbol(KwProof) {};

symbol(KwMetaDef) {};
symbol(KwMetaUndef) {};

symbol(Binder) { string name; };

symbol(ConstEquals) {};
symbol(ConstTrue) {};
symbol(ConstFalse) {};
symbol(ConstNot) {};
symbol(ConstAnd) {};
symbol(ConstOr) {};
symbol(ConstImplies) {};
symbol(ConstIff) {};

symbol(Var) { Core::Expr* e; };
symbol(Vars) { vector<Core::Expr*> es; };
symbol(Expr) { Core::Expr* e; };
symbol(WFF) { Core::Expr* e; };                    // Assumed to be verified
symbol(Proof) { Core::Expr* e; Core::Proof* pf; }; // Assumed to be verified

symbol(NewVar) { string name; };
symbol(NewVars) { vector<string> names; };
symbol(Any) {};

symbol(NewArity) { string name; unsigned short arity; };
symbol(NewArities) { vector<pair<string, unsigned short>> names; };
symbol(AnyFunc) {};
symbol(AnyPred) {};

symbol(Assumption) { string name; Core::Expr* expr; };
symbol(Assumptions) { vector<pair<string, Core::Expr*>> as; };
symbol(Assume) {};

symbol(OptRRArrow) {};
symbol(OptProof) { optional<Core::Proof*> proof; };
symbol(OptName) { optional<string> name; };
symbol(OptSemicolon) {};
symbol(Assertion) {};

symbol(MacroRuleSymbol) { pair<bool, string> s; };
symbol(MacroRule) { vector<pair<bool, string>> ss; };
symbol(MacroDef) {};
symbol(MacroUndef) {};

symbol(Decl) {};

#undef symbol


size_t Mu::wordlikePattern(const string& word) {
  auto it = wordlike.find(word);
  if (it == wordlike.end()) {
    Symbol sym = newSymbol();
    size_t pid = addPatternImpl("\"" + word + "\"", sym, lexer.word(word),
      [] (const ParseTree*) -> std::any { throw Core::Unreachable(); });
    it = wordlike.insert({ word, { pid, 0 } }).first;
  }
  it->second.second++;
  return it->second.first;
}

void Mu::removeWordlikePattern(const string& word) {
  auto it = wordlike.find(word);
  if (it == wordlike.end() || it->second.second < 1) throw Core::Unreachable();
  it->second.second--;
  if (it->second.second == 0) {
    lexer.removePattern(it->second.first);
    wordlike.erase(it);
  }
}

ParseTree* cloneParseTree(const ParseTree* x, Core::Allocator<ParseTree>& pool) {
  ParseTree* res = pool.pushBack(*x), * last = nullptr;
  res->s = nullptr;
  for (const ParseTree* p = res->c; p; p = p->s) {
    ParseTree* q = cloneParseTree(p, pool);
    (last? last->s : res->c) = q;
    last = q;
  }
  (last? last->s : res->c) = nullptr;
  return res;
}

// Ad-hoc...
ParseTree* Mu::replaceVarsByExprs(const ParseTree* x, const std::unordered_map<string, const ParseTree*> mp) {
  if (x->id == getSymbol<Var>() && x->c && x->c->id == getSymbol<Identifier>() && mp.contains(*x->c->lexeme)) {
    auto it = mp.find(*x->c->lexeme);
    if (it != mp.end()) {
      ParseTree* lparen = pool.pushBack(ParseTree{
        nullptr, nullptr,
        getSymbol<OpLParen>(),
        "(", lparenPattern, nullopt,
        x->startPos, x->startPos + 1
      });
      ParseTree* cloned = cloneParseTree(it->second, pool);
      ParseTree* rparen = pool.pushBack(ParseTree{
        nullptr, nullptr,
        getSymbol<OpRParen>(),
        ")", rparenPattern, nullopt,
        x->endPos, x->endPos + 1
      });
      ParseTree* res = pool.pushBack(ParseTree{
        nullptr, nullptr,
        getSymbol<Var>(),
        nullopt, nullopt, parenRule,
        x->startPos, x->endPos
      });
      res->c = lparen;
      lparen->s = cloned;
      cloned->s = rparen;
      rparen->s = nullptr;
      return res;
    }
  }
  ParseTree* res = pool.pushBack(*x), * last = nullptr;
  res->s = nullptr;
  for (const ParseTree* p = res->c; p; p = p->s) {
    ParseTree* q = replaceVarsByExprs(p, mp);
    (last? last->s : res->c) = q;
    last = q;
  }
  (last? last->s : res->c) = nullptr;
  return res;
}

// ====================================
// Patterns, rules and semantic actions
// ====================================

Mu::Mu() {

  // Terminal symbols

  #define epsilon     lexer.epsilon
  #define ch          lexer.ch
  #define range       lexer.range
  #define concat      lexer.concat
  #define word        lexer.word
  #define alt         lexer.alt
  #define star        lexer.star
  #define plus        lexer.plus
  #define any         lexer.any
  #define utf8segment lexer.utf8segment
  #define except      lexer.except

  #define trivial(T) [] (const string&) -> T { return {}; }

  addPattern([] (const string& lexeme) -> Natural { return { static_cast<uint32_t>(std::stoi(lexeme)) }; },
    alt({ star(range('0', '9')),
          concat(ch({ '0' }), ch({ 'x', 'X' }), star(alt({ range('0', '9'), range('a', 'f'), range('A', 'F') }))) }));
  addPattern([] (const string& lexeme) -> String { return { lexeme.substr(1, lexeme.size() - 2) }; },
    concat(ch({ '"' }), star(alt({ except({ '"', '\\' }), concat(ch({ '\\' }), ch({ '"', '\\' })) })), ch({ '"' })));
  addPattern([] (const string& lexeme) -> Identifier { return { lexeme }; },
    concat(
      alt({ range('a', 'z'), range('A', 'Z'), ch({ '_', '`' }), utf8segment() }),
      star(alt({ range('a', 'z'), range('A', 'Z'), range('0', '9'), ch({ '_', '`', '\'', '.' }), utf8segment() }))));

  addPattern(trivial(OpComma),       word(","));
  addPattern(trivial(OpSemicolon),   word(";"));
  lparenPattern =
  addPattern(trivial(OpLParen),      word("("));
  rparenPattern =
  addPattern(trivial(OpRParen),      word(")"));
  addPattern(trivial(OpLBrace),      word("{"));
  addPattern(trivial(OpRBrace),      word("}"));
  addPattern(trivial(OpRRArrow),     word("=>"));
  addPattern(trivial(OpSlash),       word("/"));
  addPattern(trivial(OpVertBar),     word("|"));
  addPattern(trivial(OpColonEq),     word(":="));

  addPattern(trivial(Blank), star(ch({ ' ', '\t', '\n', '\v', '\f', '\r' })));
  addPattern(trivial(Blank), concat(word("//"), star(except({ '\r', '\n' }))));
  addPattern(trivial(Blank),
    concat(word("/*"),
      star(concat(star(except({ '*' })), plus(ch({ '*' })), except({ '/' }))),
                  star(except({ '*' })), plus(ch({ '*' })), ch({ '/' })));

  setAsIgnoredSymbol<Blank>();

  #undef epsilon
  #undef ch
  #undef range
  #undef concat
  #undef word
  #undef alt
  #undef star
  #undef plus
  #undef any
  #undef utf8segment
  #undef except
  #undef trivial

  // Nonterminal symbols

  wordlikePatternRule("equals",     ConstEquals{});
  wordlikePatternRule("=",          ConstEquals{});
  wordlikePatternRule("true",       ConstTrue{});
  wordlikePatternRule("false",      ConstFalse{});
  wordlikePatternRule("not",        ConstNot{});
  wordlikePatternRule("and",        ConstAnd{});
  wordlikePatternRule("or",         ConstOr{});
  wordlikePatternRule("implies",    ConstImplies{});
  wordlikePatternRule("->",         ConstImplies{});
  wordlikePatternRule("iff",        ConstIff{});
  wordlikePatternRule("<->",        ConstIff{});

  wordlikePatternRule("forall",     Binder{ "forall" });
  wordlikePatternRule("exists",     Binder{ "exists" });
  wordlikePatternRule("unique",     Binder{ "unique" });
  wordlikePatternRule("forallfunc", Binder{ "forallfunc" });
  wordlikePatternRule("forallpred", Binder{ "forallpred" });

  wordlikePatternRule("any",        KwAny{});
  wordlikePatternRule("anyfunc",    KwAnyFunc{});
  wordlikePatternRule("anypred",    KwAnyPred{});
  wordlikePatternRule("assume",     KwAssume{});
  wordlikePatternRule("name",       KwName{});
  wordlikePatternRule("proof",      KwProof{});

  wordlikePatternRule("#def",       KwMetaDef{});
  wordlikePatternRule("#define",    KwMetaDef{});
  wordlikePatternRule("#undef",     KwMetaUndef{});

  #define makeExpr(...) Core::Expr::make(exprs, __VA_ARGS__)
  #define makeProof(...) Core::Proof::make(proofs, __VA_ARGS__)

  addRuleFor<Var, Identifier>([this] (const ParseTree* x) -> Var {
    string name = getChild<Identifier>(x, 0).name;
    for (size_t i = 0; i < boundVars.size(); i++) {
      if (name == boundVars[boundVars.size() - 1 - i]) {
        return { makeExprLoc(x, Core::Expr::BOUND, static_cast<unsigned int>(i)) };
      }
    }
    auto opt = ctx.lookup(name);
    if (opt.has_value()) {
      return { makeExprLoc(x, Core::Expr::FREE, opt.value()) };
    }
    throw AnalysisErrorException(x, "Undefined identifier: " + name);
  });

  addRule([]     (Var&& var)              -> Vars { return { { var.e } }; });
  addRule([]     (Vars&& vars, Var&& var) -> Vars { vars.es.push_back(var.e); return vars; });
  addRule([this] (Vars&& vars)            -> Expr {
    if (vars.es.size() < 1) throw Core::Unreachable();
    Core::Expr* res = vars.es[0];
    vars.es.erase(vars.es.begin());
    if (!vars.es.empty()) {
      sourceMap[res].second = sourceMap[vars.es.back()].second;
      res->attachChildren(vars.es);
    }
    return { res };
  }, makePrec(1.000, false));

  addRule([this] (ConstTrue)                            -> Expr { return { makeExpr(Core::Expr::TRUE) }; },
          makePrec(1.000, false));
  addRule([this] (ConstFalse)                           -> Expr { return { makeExpr(Core::Expr::FALSE) }; },
          makePrec(1.000, false));
  addRule([this] (ConstEquals, Expr&& lhs, Expr&& rhs)  -> Expr { return { makeExpr(Core::Expr::FREE, ctx.eq, vector<Core::Expr*>{ lhs.e, rhs.e }) }; },
          makePrec(0.500, false));
  addRule([this] (ConstNot, Expr&& e)                   -> Expr { return { makeExpr(Core::Expr::NOT, e.e) }; },
          makePrec(0.450, false));
  addRule([this] (Expr&& lhs, ConstAnd, Expr&& rhs)     -> Expr { return { makeExpr(Core::Expr::AND, lhs.e, rhs.e) }; },
          makePrec(0.440, false));
  addRule([this] (Expr&& lhs, ConstOr, Expr&& rhs)      -> Expr { return { makeExpr(Core::Expr::OR, lhs.e, rhs.e) }; },
          makePrec(0.430, false));
  addRule([this] (Expr&& lhs, ConstImplies, Expr&& rhs) -> Expr { return { makeExpr(Core::Expr::IMPLIES, lhs.e, rhs.e) }; },
          makePrec(0.420, true));
  addRule([this] (Expr&& lhs, ConstIff, Expr&& rhs)     -> Expr { return { makeExpr(Core::Expr::IFF, lhs.e, rhs.e) }; },
          makePrec(0.410, false));

  addRuleFor<Expr, Binder, NewVars, OpComma, Expr>([this] (const ParseTree* x) -> Expr {
    auto binder = getChild<Binder>(x, 0);
    auto names = getChild<NewVars>(x, 1).names;
    for (auto& name: names) boundVars.push_back(name);
    auto e = getChild<Expr>(x, 3).e;
    for (auto it = names.rbegin(); it != names.rend(); it++) {
      boundVars.pop_back();
      string name = *it;
      if      (binder.name == "forall") e = makeExpr(Core::Expr::FORALL, name, 0, Core::Sort::SVAR, e);
      else if (binder.name == "exists") e = makeExpr(Core::Expr::EXISTS, name, 0, Core::Sort::SVAR, e);
      else if (binder.name == "unique") e = makeExpr(Core::Expr::UNIQUE, name, 0, Core::Sort::SVAR, e);
      else if (binder.name == "forallfunc") e = makeExpr(Core::Expr::FORALL2, name, 1, Core::Sort::SVAR, e);
      else if (binder.name == "forallpred") e = makeExpr(Core::Expr::FORALL2, name, 1, Core::Sort::SPROP, e);
      else throw Core::Unreachable();
    }
    return { e };
  }, makePrec(0.100, false));
  addRuleFor<Expr, Binder, NewArities, OpComma, Expr>([this] (const ParseTree* x) -> Expr {
    auto binder = getChild<Binder>(x, 0);
    auto names = getChild<NewArities>(x, 1).names;
    for (auto& [name, _]: names) boundVars.push_back(name);
    auto e = getChild<Expr>(x, 3).e;
    for (auto it = names.rbegin(); it != names.rend(); it++) {
      boundVars.pop_back();
      string name = it->first; unsigned short arity = it->second;
      if      (binder.name == "forall") e = makeExpr(Core::Expr::FORALL, name, arity, Core::Sort::SVAR, e);
      else if (binder.name == "exists") e = makeExpr(Core::Expr::EXISTS, name, arity, Core::Sort::SVAR, e);
      else if (binder.name == "unique") e = makeExpr(Core::Expr::UNIQUE, name, arity, Core::Sort::SVAR, e);
      else if (binder.name == "forallfunc") e = makeExpr(Core::Expr::FORALL2, name, arity, Core::Sort::SVAR, e);
      else if (binder.name == "forallpred") e = makeExpr(Core::Expr::FORALL2, name, arity, Core::Sort::SPROP, e);
      else throw Core::Unreachable();
    }
    return { e };
  }, makePrec(0.100, false));
  /*
  // TODO: lambdas
  addRuleFor<Var, Vars, OpVertBar, Term>([this] (const ParseTree* x) -> Var {
    vector<Core::Expr*> vars = getChild<Vars>(x, 0).es;
  });
  */
  parenRule =
  addRule([] (OpLParen, Expr&& e, OpRParen) -> Var { return { e.e }; });

  addRuleFor<WFF, Expr>([this] (const ParseTree* x) -> WFF {
    boundVars.clear();
    auto e = getChild<Expr>(x, 0).e;
    try {
      auto t = e->checkType(ctx);
    } catch(Core::InvalidExpr& ex) {
      // TODO: lookup in sourceMap (replace those `makeExpr` by `makeExprLoc` first)
      throw AnalysisErrorException(x, e->toString(ctx) + ":\n" + ex.what());
    }
    info.emplace_back(x, e->toString(ctx) + ": wff"); // DEBUG CODE
    return { e };
  });

  addRule([]     (Identifier&& id)                   -> NewVar { return { id.name }; });
  addRule([]     (NewVar&& v)                        -> NewVars { return { { v.name } }; });
  addRule([]     (NewVars&& vs, OpComma)             -> NewVars { return vs; });
  addRule([]     (NewVars&& vs, OpComma, NewVar&& v) -> NewVars { vs.names.push_back(v.name); return vs; });
  addRuleFor<Any, KwAny, NewVars>([this] (const ParseTree* x) -> Any {
    auto names = getChild<NewVars>(x, 1).names;
    for (auto& name: names) ctx.pushVar(name, Core::Type{{ 0, Core::Sort::SVAR }});
    scopes.emplace_back(names.size(), 0);
    immediate = true;
    return {};
  });

  addRule([]     (Identifier&& id, OpSlash, Natural&& n)  -> NewArity { return { id.name, static_cast<unsigned short>(n.data) }; });
  addRule([]     (NewArity&& f)                           -> NewArities { return { { { f.name, f.arity } } }; });
  addRule([]     (NewArities&& fs, OpComma)               -> NewArities { return fs; });
  addRule([]     (NewArities&& fs, OpComma, NewArity&& f) -> NewArities { fs.names.emplace_back(f.name, f.arity); return fs; });
  addRuleFor<AnyFunc, KwAnyFunc, NewArities>([this] (const ParseTree* x) -> AnyFunc {
    auto fs = getChild<NewArities>(x, 1).names;
    for (auto& [name, arity]: fs) ctx.pushVar(name, Core::Type{{ arity, Core::Sort::SVAR }});
    scopes.emplace_back(fs.size(), 0);
    immediate = true;
    return {};
  });
  addRuleFor<AnyPred, KwAnyPred, NewArities>([this] (const ParseTree* x) -> AnyPred {
    auto ps = getChild<NewArities>(x, 1).names;
    for (auto& [name, arity]: ps) ctx.pushVar(name, Core::Type{{ arity, Core::Sort::SPROP }});
    scopes.emplace_back(ps.size(), 0);
    immediate = true;
    return {};
  });

  addRule([]     (WFF&& e, OptName&& name)                   -> Assumption { return { name.name.value_or(""), e.e }; });
  addRule([]     (Assumption&& a)                            -> Assumptions { return { { { a.name, a.expr } } }; });
  addRule([]     (Assumptions&& as, OpComma)                 -> Assumptions { return as; });
  addRule([]     (Assumptions&& as, OpComma, Assumption&& a) -> Assumptions { as.as.emplace_back(a.name, a.expr); return as; });
  addRuleFor<Assume, KwAssume, Assumptions>([this] (const ParseTree* x) -> Assume {
    auto as = getChild<Assumptions>(x, 1).as;
    for (auto& [name, e]: as) ctx.pushAssumption(name, e);
    scopes.emplace_back(as.size(), 0);
    immediate = true;
    return {};
  });

  addRule([]     ()                        -> OptRRArrow { return {}; });
  addRule([]     (OpRRArrow)               -> OptRRArrow { return {}; });
  addRule([]     ()                        -> OptProof { return { nullopt }; });
  addRule([]     (KwProof, Proof&& pf)     -> OptProof { return { pf.pf }; });
  addRule([]     ()                        -> OptName { return { nullopt }; });
  addRule([]     (KwName, Identifier&& id) -> OptName { return { id.name }; });
  addRule([]     ()                        -> OptSemicolon { return {}; });
  addRule([]     (OpSemicolon)             -> OptSemicolon { return {}; });
  addRule([this] (OptRRArrow, WFF&&, OptName&&, OptProof&&, OptSemicolon) -> Assertion {
    // TODO: verify or start tableau thread
    return {};
  });

  addRule([]     (String&& s)                          -> MacroRuleSymbol { return { { true, s.data } }; });
  addRule([]     (Identifier&& s)                      -> MacroRuleSymbol { return { { false, s.name } }; });
  addRule([]     (MacroRuleSymbol&& s)                 -> MacroRule { return { { s.s } }; });
  addRule([]     (MacroRule&& ss, MacroRuleSymbol&& s) -> MacroRule { ss.ss.push_back(s.s); return ss; });
  addRuleFor<MacroDef, KwMetaDef, MacroRule, OpColonEq, Expr, KwName, Identifier, OptSemicolon>([this] (const ParseTree* x) -> MacroDef {
    auto pattern = getChild<MacroRule>(x, 1).ss;
    string rulename = getChild<Identifier>(x, 5).name;
    const ParseTree* term = x->c->s->s->s;
    std::unordered_map<string, size_t> positions;
    // Generate new production rule from the given pattern
    vector<Parsing::Symbol> rhs;
    vector<string> words;
    for (size_t i = 0; i < pattern.size(); i++) {
      string name = pattern[i].second;
      if (pattern[i].first) {
        // Terminal
        Symbol sym = lexer.patternSymbol(wordlikePattern(name));
        rhs.push_back(sym);
        words.push_back(name);
      } else {
        // Argument
        positions[name] = i;
        rhs.push_back(getSymbol<Expr>());
      }
    }
    // Add handler for this new rule
    size_t rid = addRuleImpl(SymbolName<Expr>::get(), getSymbol<Expr>(), rhs, [this, term, positions] (const ParseTree* x) -> Expr {
      std::unordered_map<string, const ParseTree*> mp;
      for (auto& [key, val]: positions) {
        const ParseTree* p = x->c;
        for (size_t i = 0; i < val; i++) p = p->s;
        mp[key] = p;
      }
      ParseTree* transformed = replaceVarsByExprs(term, mp);
      return get<Expr>(transformed);
    }, makePrec(0.5, false));
    // Add record
    customParsingRules[rulename] = { rid, words };
    return {};
  });
  addRuleFor<MacroUndef, KwMetaUndef, Identifier, OptSemicolon>([this] (const ParseTree* x) -> MacroUndef {
    string name = getChild<Identifier>(x, 1).name;
    auto it = customParsingRules.find(name);
    if (it == customParsingRules.end()) {
      errors.emplace_back(x, "Unknown parsing rule \"" + name + "\"");
    } else {
      parser.rules[it->second.first].active = false;
      for (const string& word: it->second.second) removeWordlikePattern(word);
      customParsingRules.erase(it);
    }
    return {};
  });

  addRule([]     (Assertion)                 -> Decl { return {}; });
  addRule([]     (Assume)                    -> Decl { return {}; });
  addRule([]     (Any)                       -> Decl { return {}; });
  addRule([]     (AnyFunc)                   -> Decl { return {}; });
  addRule([]     (AnyPred)                   -> Decl { return {}; });
  addRule([]     (MacroDef)                  -> Decl { return {}; });
  addRule([]     (MacroUndef)                -> Decl { return {}; });

  addRuleFor<Decl, OpLBrace>([this] (const ParseTree*) -> Decl {
    if (scopes.empty()) throw Core::Unreachable();
    scopes.back().second++;
    return {};
  });
  addRuleFor<Decl, OpRBrace>([this] (const ParseTree* x) -> Decl {
    if (scopes.empty()) throw Core::Unreachable();
    if (scopes.size() == 1 && scopes.back().second <= 1) throw AnalysisErrorException(x, "Unexpected closing brace");
    scopes.back().second--;
    return {};
  });

  #undef makeExpr
  #undef makeProof

  /*
  // Test ambiguity detection (use `=> $B $B $B;` to trigger)
  struct A {};
  struct B {};

  addPattern([] (const string&) -> B { return {}; }, word("$B"));
  addRule([] (A, A) -> A { return {}; });
  addRule([] (B) -> A { return {}; });
  addRule([] (A) -> Expr { return {}; });
  */
}


// =======================
// Root symbol declaration
// =======================

void Mu::analyze(const string& str) {
  scopes.emplace_back(0, 1);
  lexer.setString(str);
  while (!parser.eof()) {
    immediate = false;
    try {
      Language::nextSentence<Decl>();
    } catch (AnalysisErrorException& ex) {
      errors.push_back(ex);
    }
    /*
    vector<string> names;
    std::for_each(symbols.begin(), symbols.end(), [&] (const Entry& e) { names.push_back(e.name); });
    std::cerr << parser.showStates(names) << std::endl;
    */
    if (!immediate) {
      while (!scopes.empty() && scopes.back().second == 0) {
        for (size_t i = 0; i < scopes.back().first; i++) ctx.pop(exprs);
        scopes.pop_back();
      }
    }
  }
}

vector<Mu::AnalysisInfo> Mu::popAnalysisInfo() {
  vector<AnalysisInfo> res;
  res.swap(info);
  return res;
}

vector<Mu::AnalysisErrorException> Mu::popAnalysisErrors() {
  vector<AnalysisErrorException> res;
  res.swap(errors);
  return res;
}
