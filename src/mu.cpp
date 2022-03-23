#include "mu.hpp"
#include <optional>
#include <variant>
#include <iostream>

using std::string;
using std::vector;
using std::pair, std::make_pair;
using std::optional, std::make_optional, std::nullopt;
using std::variant, std::get, std::holds_alternative;
using Parsing::ParseTree;


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

symbol(KwAny) {};
symbol(KwAnyFunc) {};
symbol(KwAnyPred) {};
symbol(KwAssume) {};
symbol(KwName) {};
symbol(KwProof) {};

symbol(KwMetaDef) {};
symbol(KwMetaUndef) {};

symbol(Constant) { string name; };
symbol(Infix80) { string name; };
symbol(Infix60) { string name; };
symbol(Infix40) { string name; };
symbol(Prefix30) { string name; };
symbol(Infix20) { string name; };

symbol(Binder) { string name; };
symbol(Identifier) { string name; };

// Nonterminal symbols

symbol(Var) { Core::Expr* e; };
symbol(Vars) { vector<Core::Expr*> es; };
symbol(Term100) { Core::Expr* e; };
symbol(Term80) { Core::Expr* e; };
symbol(Term60) { Core::Expr* e; };
symbol(Term40) { Core::Expr* e; };
symbol(Term30) { Core::Expr* e; };
symbol(Term20) { Core::Expr* e; };
symbol(Term10) { Core::Expr* e; };
symbol(Term10Suffix) { Core::Expr* e; };
symbol(Term10OrSuffix) { Core::Expr* e; };
symbol(Term) { Core::Expr* e; };

symbol(Expr) { Core::Expr* e; };                   // Assumed to be verified
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
ParseTree* Mu::replaceVarsByTerms(const ParseTree* x, const std::unordered_map<string, const ParseTree*> mp) {
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
    ParseTree* q = replaceVarsByTerms(p, mp);
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

  // Terminal symbols (TODO: disambiguate based on pattern ID instead of symbol ID)

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
  addPattern([] (const string& lexeme) -> Binder { return { lexeme }; },
    alt({ word("forall"), word("exists"), word("unique"), word("forallfunc"), word("forallpred") }));

  addPattern(trivial(KwAny),         word("any"));
  addPattern(trivial(KwAnyFunc),     word("anyfunc"));
  addPattern(trivial(KwAnyPred),     word("anypred"));
  addPattern(trivial(KwAssume),      word("assume"));
  addPattern(trivial(KwName),        word("name"));
  addPattern(trivial(KwProof),       word("proof"));

  addPattern(trivial(KwMetaDef),     word("#def"));
  addPattern(trivial(KwMetaUndef),   word("#undef"));

  addPattern([] (const string& lexeme) -> Infix80 { return { lexeme }; }, ch({ '*', '\\', '%', '^', }));
  addPattern([] (const string& lexeme) -> Infix60 { return { lexeme }; }, ch({ '+', '-' }));
  addPattern([] (const string& lexeme) -> Infix40 { return { lexeme }; }, alt({ ch({ '=', '<', '>' }), word("!="), word(">="), word("<=") }));
  addPattern([] (const string& lexeme) -> Constant { return { lexeme }; },
    alt({ word("true"), word("false") }));
  addPattern([] (const string& lexeme) -> Prefix30 { return { lexeme }; },
    alt({ word("not") }));
  addPattern([] (const string& lexeme) -> Infix20 { return { lexeme }; },
    alt({ word("and"), word("or"), word("implies"), word("iff"), word("->"), word("<->") }));

  addPattern(trivial(OpComma),       word(","));
  addPattern(trivial(OpSemicolon),   word(";"));
  lparenPattern = addPattern(trivial(OpLParen),      word("("));
  rparenPattern = addPattern(trivial(OpRParen),      word(")"));
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

  #define makeExpr(...) Core::Expr::make(exprs, __VA_ARGS__)
  #define makeProof(...) Core::Proof::make(proofs, __VA_ARGS__)

  addRuleFor<Var, Constant>([this] (const ParseTree* x) -> Var {
    auto c = getChild<Constant>(x, 0);
    if (c.name == "true") return { makeExpr(Core::Expr::TRUE) };
    if (c.name == "false") return { makeExpr(Core::Expr::FALSE) };
    throw AnalysisErrorException(x, "Unknown constant: " + c.name);
  });
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
  addRule([this] (Vars&& vars)            -> Term100 {
    if (vars.es.size() < 1) throw Core::Unreachable();
    Core::Expr* res = vars.es[0];
    vars.es.erase(vars.es.begin());
    if (!vars.es.empty()) {
      sourceMap[res].second = sourceMap[vars.es.back()].second;
      res->attachChildren(vars.es);
    }
    return { res };
  });

  addRule([]     (Term100&& t)                              -> Term80 { return { t.e }; });
  addRule([this] (Term80&& lhs, Infix80&&, Term100&& rhs)   -> Term80 { return { makeExpr(Core::Expr::FREE, ctx.eq, vector<Core::Expr*>{ lhs.e, rhs.e }) }; }); // TODO: lookup table
  addRule([]     (Term80&& t)                               -> Term60 { return { t.e }; });
  addRule([this] (Term60&& lhs, Infix60&&, Term80&& rhs)    -> Term60 { return { makeExpr(Core::Expr::FREE, ctx.eq, vector<Core::Expr*>{ lhs.e, rhs.e }) }; });
  addRule([]     (Term60&& t)                               -> Term40 { return { t.e }; });
  addRule([this] (Term40&& lhs, Infix40&&, Term60&& rhs)    -> Term40 { return { makeExpr(Core::Expr::FREE, ctx.eq, vector<Core::Expr*>{ lhs.e, rhs.e }) }; });
  addRule([]     (Term40&& t)                               -> Term30 { return { t.e }; });
  addRuleFor<Term30, Prefix30, Term30>([this] (const ParseTree* x) -> Term30 {
    auto op = getChild<Prefix30>(x, 0);
    auto t = getChild<Term30>(x, 1);
    if (op.name == "not") return { makeExpr(Core::Expr::NOT, t.e) };
    throw AnalysisErrorException(x, "Unknown connective: " + op.name);
  });
  addRule([]     (Term30&& t)                               -> Term20 { return { t.e }; });
  addRuleFor<Term20, Term20, Infix20, Term30>([this] (const ParseTree* x) -> Term20 {
    auto lhs = getChild<Term20>(x, 0);
    auto op = getChild<Infix20>(x, 1);
    auto rhs = getChild<Term30>(x, 2);
    if (op.name == "and") return { makeExpr(Core::Expr::AND, lhs.e, rhs.e) };
    if (op.name == "or") return { makeExpr(Core::Expr::OR, lhs.e, rhs.e) };
    if (op.name == "implies" || op.name == "->") return { makeExpr(Core::Expr::IMPLIES, lhs.e, rhs.e) };
    if (op.name == "iff" || op.name == "<->") return { makeExpr(Core::Expr::IFF, lhs.e, rhs.e) };
    throw AnalysisErrorException(x, "Unknown connective: " + op.name);
  });
  addRule([]     (Term20&& t)                               -> Term10 { return { t.e }; });
  addRuleFor<Term10Suffix, Binder, NewVars, OpComma, Term10OrSuffix>([this] (const ParseTree* x) -> Term10Suffix {
    auto binder = getChild<Binder>(x, 0);
    auto names = getChild<NewVars>(x, 1).names;
    for (auto& name: names) boundVars.push_back(name);
    auto e = getChild<Term10OrSuffix>(x, 3).e;
    for (auto it = names.rbegin(); it != names.rend(); it++) {
      boundVars.pop_back();
      string name = *it;
      if (binder.name == "forall") e = makeExpr(Core::Expr::FORALL, name, 0, Core::Sort::SVAR, e);
      else if (binder.name == "exists") e = makeExpr(Core::Expr::EXISTS, name, 0, Core::Sort::SVAR, e);
      else if (binder.name == "unique") e = makeExpr(Core::Expr::UNIQUE, name, 0, Core::Sort::SVAR, e);
      else if (binder.name == "forallfunc") e = makeExpr(Core::Expr::FORALL2, name, 1, Core::Sort::SVAR, e);
      else if (binder.name == "forallpred") e = makeExpr(Core::Expr::FORALL2, name, 1, Core::Sort::SPROP, e);
      else throw AnalysisErrorException(x, "Unknown connective: " + binder.name);
    }
    return { e };
  });
  addRuleFor<Term10Suffix, Binder, NewArities, OpComma, Term10OrSuffix>([this] (const ParseTree* x) -> Term10Suffix {
    auto binder = getChild<Binder>(x, 0);
    auto names = getChild<NewArities>(x, 1).names;
    for (auto& [name, _]: names) boundVars.push_back(name);
    auto e = getChild<Term10OrSuffix>(x, 3).e;
    for (auto it = names.rbegin(); it != names.rend(); it++) {
      boundVars.pop_back();
      string name = it->first; unsigned short arity = it->second;
      if (binder.name == "forall") e = makeExpr(Core::Expr::FORALL, name, arity, Core::Sort::SVAR, e);
      else if (binder.name == "exists") e = makeExpr(Core::Expr::EXISTS, name, arity, Core::Sort::SVAR, e);
      else if (binder.name == "unique") e = makeExpr(Core::Expr::UNIQUE, name, arity, Core::Sort::SVAR, e);
      else if (binder.name == "forallfunc") e = makeExpr(Core::Expr::FORALL2, name, arity, Core::Sort::SVAR, e);
      else if (binder.name == "forallpred") e = makeExpr(Core::Expr::FORALL2, name, arity, Core::Sort::SPROP, e);
      else throw AnalysisErrorException(x, "Unknown connective: " + binder.name);
    }
    return { e };
  });
  addRule([]     (Term10Suffix&& t)                         -> Term10OrSuffix { return { t.e }; });
  addRule([]     (Term10&& t)                               -> Term10OrSuffix { return { t.e }; });
  // TEMP CODE
  addRuleFor<Term10Suffix, Prefix30, Term10Suffix>([this] (const ParseTree* x) -> Term10Suffix {
    auto op = getChild<Prefix30>(x, 0);
    auto t = getChild<Term10Suffix>(x, 1);
    if (op.name == "not") return { makeExpr(Core::Expr::NOT, t.e) };
    throw AnalysisErrorException(x, "Unknown connective: " + op.name);
  });
  // TEMP CODE
  addRuleFor<Term10, Term20, Infix20, Term10Suffix>([this] (const ParseTree* x) -> Term10 {
    auto lhs = getChild<Term20>(x, 0);
    auto op = getChild<Infix20>(x, 1);
    auto rhs = getChild<Term10Suffix>(x, 2);
    if (op.name == "and") return { makeExpr(Core::Expr::AND, lhs.e, rhs.e) };
    if (op.name == "or") return { makeExpr(Core::Expr::OR, lhs.e, rhs.e) };
    if (op.name == "implies" || op.name == "->") return { makeExpr(Core::Expr::IMPLIES, lhs.e, rhs.e) };
    if (op.name == "iff" || op.name == "<->") return { makeExpr(Core::Expr::IFF, lhs.e, rhs.e) };
    throw AnalysisErrorException(x, "Unknown connective: " + op.name);
  });
  /*
  // TODO: lambdas
  addRuleFor<Var, Vars, OpVertBar, Term>([this] (const ParseTree* x) -> Var {
    vector<Core::Expr*> vars = getChild<Vars>(x, 0).es;
  });
  */
  addRule([] (Term10&& t)                   -> Term { return { t.e }; });
  addRule([] (Term10Suffix&& t)             -> Term { return { t.e }; });
  parenRule = addRule([] (OpLParen, Term&& t, OpRParen) -> Var { return { t.e }; });

  addRuleFor<Expr, Term>([this] (const ParseTree* x) -> Expr {
    boundVars.clear();
    auto e = getChild<Term>(x, 0).e;
    try {
      auto t = e->checkType(ctx);
    } catch(Core::InvalidExpr& ex) {
      // TODO: lookup in sourceMap (replace those `makeExpr` by `makeExprLoc` first)
      throw AnalysisErrorException(x, ex.what());
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

  addRule([]     (Expr&& e, OptName&& name)                  -> Assumption { return { name.name.value_or(""), e.e }; });
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
  addRule([this] (OptRRArrow, Expr&&, OptName&&, OptProof&&, OptSemicolon) -> Assertion {
    // TODO: verify or start tableau thread
    return {};
  });

  addRule([]     (String&& s)                          -> MacroRuleSymbol { return { { true, s.data } }; });
  addRule([]     (Identifier&& s)                      -> MacroRuleSymbol { return { { false, s.name } }; });
  addRule([]     (MacroRuleSymbol&& s)                 -> MacroRule { return { { s.s } }; });
  addRule([]     (MacroRule&& ss, MacroRuleSymbol&& s) -> MacroRule { ss.ss.push_back(s.s); return ss; });
  addRuleFor<MacroDef, KwMetaDef, MacroRule, OpColonEq, Term30, KwName, Identifier, OptSemicolon>([this] (const ParseTree* x) -> MacroDef {
    auto pattern = getChild<MacroRule>(x, 1).ss;
    string rulename = getChild<Identifier>(x, 5).name;
    const ParseTree* term = x->c->s->s->s;
    std::unordered_map<string, size_t> positions;
    // Generate new production rule from the given pattern
    vector<Parsing::Symbol> rhs;
    for (size_t i = 0; i < pattern.size(); i++) {
      string name = pattern[i].second;
      if (pattern[i].first) {
        // Terminal (TODO: pattern removal from lexer...)
        if (!terminals.contains(name)) {
          Parsing::Symbol sym = newSymbol(name, [] (const ParseTree*) -> std::any { return {}; });
          lexer.addPattern(sym, lexer.word(name));
          terminals[name] = sym;
        }
        rhs.push_back(terminals[name]);
      } else {
        // Argument
        positions[name] = i;
        rhs.push_back(getSymbol<Term>());
      }
    }
    // Add handler for this new rule
    size_t rid = addRuleImpl("term30", getSymbol<Term30>(), rhs, [this, term, positions] (const ParseTree* x) -> Term30 {
      std::unordered_map<string, const ParseTree*> mp;
      for (auto& [key, val]: positions) {
        const ParseTree* p = x->c;
        for (size_t i = 0; i < val; i++) p = p->s;
        mp[key] = p;
      }
      ParseTree* transformed = replaceVarsByTerms(term, mp);
      return get<Term30>(transformed);
    });
    customParsingRules[rulename] = rid;
    return {};
  });
  addRuleFor<MacroUndef, KwMetaUndef, Identifier, OptSemicolon>([this] (const ParseTree* x) -> MacroUndef {
    string name = getChild<Identifier>(x, 1).name;
    auto it = customParsingRules.find(name);
    if (it == customParsingRules.end()) {
      errors.emplace_back(x, "Unknown parsing rule \"" + name + "\"");
    } else {
      parser.rules[it->second].active = false;
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
