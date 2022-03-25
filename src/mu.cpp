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

// See: https://en.cppreference.com/w/cpp/utility/variant/visit
template <class... Ts> struct Matcher: Ts... { using Ts::operator()...; };


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
symbol(Decimal) { double data; };
symbol(String) { string data; };

symbol(OpLParen) {};
symbol(OpRParen) {};

symbol(Identifier) { string name; };

// Nonterminal symbols

symbol(OpComma) {};
symbol(OpSemicolon) {};
symbol(OpLBrace) {};
symbol(OpRBrace) {};
symbol(OpRRArrow) {};
symbol(OpSlash) {};
symbol(OpVertBar) {};
symbol(OpColonEq) {};
symbol(OpColonColon) {};

symbol(KwAny) {};
symbol(KwAnyFunc) {};
symbol(KwAnyPred) {};
symbol(KwAssume) {};
symbol(KwName) {};
symbol(KwProof) {};
symbol(KwDef) {};
symbol(KwIdef) {};
symbol(KwUndef) {};
symbol(KwPrec) {};
symbol(KwRightmostLongest) {};
symbol(KwRightmostShortest) {};
symbol(KwMetaList) {};
symbol(KwMetaDef) {};
symbol(KwMetaUndef) {};

symbol(ConstEquals) {};
symbol(ConstTrue) {};
symbol(ConstFalse) {};
symbol(ConstNot) {};
symbol(ConstAnd) {};
symbol(ConstOr) {};
symbol(ConstImplies) {};
symbol(ConstIff) {};
symbol(Quantifier) { Core::Expr::Tag tag; };
symbol(Quantifier2) { Core::Expr::Tag tag; Core::Sort sort; };

/*
symbol(ProofAndI) {};
symbol(ProofAndL) {};
symbol(ProofAndR) {};
symbol(ProofOrL) {};
symbol(ProofOrR) {};
symbol(ProofOrE) {};
symbol(ProofImpliesE) {};
symbol(ProofNotI) {};
symbol(ProofNotE) {};
symbol(ProofIffI) {};
symbol(ProofIffL) {};
symbol(ProofIffR) {};
symbol(ProofTrueI) {};
symbol(ProofFalseE) {};
symbol(ProofRAA) {};
symbol(ProofEqualsI) {};
symbol(ProofEqualsE) {};
symbol(ProofForallE) {};
symbol(ProofExistsI) {};
symbol(ProofExistsE) {};
symbol(ProofUniqueI) {};
symbol(ProofUniqueL) {};
symbol(ProofUniqueR) {};
symbol(ProofForall2E) {};
*/

symbol(Var) { Core::Expr* e; };
symbol(Vars) { vector<Core::Expr*> es; };
symbol(Expr) { Core::Expr* e; };
symbol(Proof) { Core::Proof* pf; };

symbol(WFE) { Core::Expr* e; Core::Type t; };
symbol(WFF) { Core::Expr* e; };
symbol(WFP) { Core::Proof* pf; Core::Expr* e; };

symbol(NewVar) { string name; };
symbol(NewVars) { vector<string> names; };
symbol(NewArity) { string name; unsigned short arity; };
symbol(NewArities) { vector<pair<string, unsigned short>> names; };
symbol(Assumption) { string name; Core::Expr* expr; };
symbol(Assumptions) { vector<pair<string, Core::Expr*>> as; };
symbol(Any) {};
symbol(AnyFunc) {};
symbol(AnyPred) {};
symbol(Assume) {};

symbol(OptRRArrow) {};
symbol(OptProof) { optional<WFP> pf; };
symbol(OptName) { optional<string> name; };
symbol(OptSemicolon) {};
symbol(Assertion) {};

symbol(Def) {};
symbol(DDef) {};
symbol(Idef) {};
symbol(Undef) {};

symbol(List) {};
symbol(MacroRuleSymbol) { pair<bool, string> s; };
symbol(MacroRule) { vector<pair<bool, string>> ss; };
symbol(OptPrec) { optional<double> prec; };
symbol(OptAssoc) { int f; };
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
  #define opt         lexer.opt
  #define plus        lexer.plus
  #define any         lexer.any
  #define utf8segment lexer.utf8segment
  #define except      lexer.except

  addPattern([] (const string& lexeme) -> Natural { return { static_cast<uint32_t>(std::stoi(lexeme)) }; },
    alt(plus(range('0', '9')),
        concat(ch('0'), ch('x', 'X'), plus(alt(range('0', '9'), range('a', 'f'), range('A', 'F'))))));
  addPattern([] (const string& lexeme) -> Decimal { return { static_cast<double>(std::stod(lexeme)) }; },
    alt(concat(opt(ch('+', '-')),
          plus(range('0', '9')), ch('.'),
          star(range('0', '9')),
          opt(concat(ch('e', 'E'), opt(ch('+', '-')), plus(range('0', '9'))))),
        concat(opt(ch('+', '-')), ch('0'), ch('x', 'X'),
          plus(alt(range('0', '9'), range('a', 'f'), range('A', 'F'))), ch('.'),
          star(alt(range('0', '9'), range('a', 'f'), range('A', 'F'))),
          opt(concat(ch('p', 'P'), opt(ch('+', '-')), plus(range('0', '9')))))));
  addPattern([] (const string& lexeme) -> String { return { lexeme.substr(1, lexeme.size() - 2) }; },
    concat(ch('"'), star(alt(except('"', '\\'), concat(ch('\\'), ch('"', '\\')))), ch('"')));
  addPattern([] (const string& lexeme) -> Identifier { return { lexeme }; },
    concat(alt(range('a', 'z'), range('A', 'Z'), ch('_', '`'), utf8segment()),
      star(alt(range('a', 'z'), range('A', 'Z'), range('0', '9'), ch('_', '`', '\'', '.'), utf8segment()))));
  addPattern([] (const string&) -> Blank { return {}; },
    star(ch(' ', '\t', '\n', '\v', '\f', '\r')));
  addPattern([] (const string&) -> Blank { return {}; },
    concat(word("//"), star(except('\r', '\n'))));
  addPattern([] (const string&) -> Blank { return {}; },
    concat(word("/*"),
      star(concat(star(except('*')), plus(ch('*')), except('/'))),
                  star(except('*')), plus(ch('*')), ch('/')));
  setAsIgnoredSymbol<Blank>();

  lparenPattern = addPattern([] (const string&) -> OpLParen { return {}; }, word("("));
  rparenPattern = addPattern([] (const string&) -> OpRParen { return {}; }, word(")"));

  #undef epsilon
  #undef ch
  #undef range
  #undef concat
  #undef word
  #undef alt
  #undef star
  #undef opt
  #undef plus
  #undef any
  #undef utf8segment
  #undef except
  #undef trivial

  // These can be overriden by macros

  wordlikePatternRule(",",            OpComma{});
  wordlikePatternRule(";",            OpSemicolon{});
  wordlikePatternRule("{",            OpLBrace{});
  wordlikePatternRule("}",            OpRBrace{});
  wordlikePatternRule("=>",           OpRRArrow{});
  wordlikePatternRule("/",            OpSlash{});
  wordlikePatternRule("|",            OpVertBar{});
  wordlikePatternRule(":=",           OpColonEq{});
  wordlikePatternRule("::",           OpColonColon{});

  wordlikePatternRule("equals",       ConstEquals{});
  wordlikePatternRule("=",            ConstEquals{});
  wordlikePatternRule("true",         ConstTrue{});
  wordlikePatternRule("false",        ConstFalse{});
  wordlikePatternRule("not",          ConstNot{});
  wordlikePatternRule("and",          ConstAnd{});
  wordlikePatternRule("or",           ConstOr{});
  wordlikePatternRule("implies",      ConstImplies{});
  wordlikePatternRule("->",           ConstImplies{});
  wordlikePatternRule("iff",          ConstIff{});
  wordlikePatternRule("<->",          ConstIff{});

  wordlikePatternRule("forall",       Quantifier{ Core::Expr::FORALL });
  wordlikePatternRule("exists",       Quantifier{ Core::Expr::EXISTS });
  wordlikePatternRule("unique",       Quantifier{ Core::Expr::UNIQUE });
  wordlikePatternRule("forallfunc",   Quantifier2{ Core::Expr::FORALL2, Core::Sort::SVAR });
  wordlikePatternRule("forallpred",   Quantifier2{ Core::Expr::FORALL2, Core::Sort::SPROP });

/*
  wordlikePatternRule("and.i",        ProofAndI{});
  wordlikePatternRule("and.l",        ProofAndL{});
  wordlikePatternRule("and.r",        ProofAndR{});
  wordlikePatternRule("or.l",         ProofOrL{});
  wordlikePatternRule("or.r",         ProofOrR{});
  wordlikePatternRule("or.e",         ProofOrE{});
  wordlikePatternRule("implies.e",    ProofImpliesE{});
  wordlikePatternRule("not.i",        ProofNotI{});
  wordlikePatternRule("not.e",        ProofNotE{});
  wordlikePatternRule("iff.i",        ProofIffI{});
  wordlikePatternRule("iff.l",        ProofIffL{});
  wordlikePatternRule("iff.r",        ProofIffR{});
  wordlikePatternRule("true.i",       ProofTrueI{});
  wordlikePatternRule("false.e",      ProofFalseE{});
  wordlikePatternRule("raa",          ProofRAA{});
  wordlikePatternRule("equals.i",     ProofEqualsI{});
  wordlikePatternRule("equals.e",     ProofEqualsE{});
  wordlikePatternRule("forall.e",     ProofForallE{});
  wordlikePatternRule("exists.i",     ProofExistsI{});
  wordlikePatternRule("exists.e",     ProofExistsE{});
  wordlikePatternRule("unique.i",     ProofUniqueI{});
  wordlikePatternRule("unique.l",     ProofUniqueL{});
  wordlikePatternRule("unique.r",     ProofUniqueR{});
  wordlikePatternRule("forallfunc.e", ProofForall2E{});
  wordlikePatternRule("forallpred.e", ProofForall2E{});
*/

  wordlikePatternRule("any",          KwAny{});
  wordlikePatternRule("anyfunc",      KwAnyFunc{});
  wordlikePatternRule("anypred",      KwAnyPred{});
  wordlikePatternRule("assume",       KwAssume{});
  wordlikePatternRule("name",         KwName{});
  wordlikePatternRule("proof",        KwProof{});
  wordlikePatternRule("def",          KwDef{});
  wordlikePatternRule("idef",         KwIdef{});
  wordlikePatternRule("undef",        KwUndef{});
  wordlikePatternRule("prec",         KwPrec{});
  wordlikePatternRule("right_assoc",  KwRightmostLongest{});
  wordlikePatternRule("left_assoc",   KwRightmostShortest{});
  wordlikePatternRule("#ls",          KwMetaList{});
  wordlikePatternRule("#list",        KwMetaList{});
  wordlikePatternRule("#def",         KwMetaDef{});
  wordlikePatternRule("#define",      KwMetaDef{});
  wordlikePatternRule("#undef",       KwMetaUndef{});

  // Nonterminal symbols

  #define makeExpr(...) Core::Expr::make(exprs, __VA_ARGS__)
  #define makeProof(...) Core::Proof::make(proofs, __VA_ARGS__)

  // `addRuleFor`: uses explicit collector
  // Rule: `[var] ::= <identifier>`
  // Collector: constructs a `Var` object from an `Identifier` object, allowing reference to the `ParseTree` node
  addRuleFor<Var, Identifier>
  ([this] (const ParseTree* x) {
    string name = getChild<Identifier>(x, 0).name;
    for (size_t i = 0; i < boundVars.size(); i++) {
      const auto& v = boundVars[boundVars.size() - 1 - i];
      if (name == v.first) {
        result.hovers.emplace_back(x, "", v.first + ": " + Core::showType(v.second));
        result.tokens.emplace_back(x);
        auto it = defMap.find(v.first);
        if (it != defMap.end()) result.tokens.back().defPos = it->second;
        return Var{ makeExprLoc(x, Core::Expr::BOUND, static_cast<unsigned int>(i)) };
      }
    }
    auto opt = ctx.lookup(name);
    if (opt.has_value()) {
      result.hovers.emplace_back(x, "", name + ": " + std::visit(Matcher{
        [&] (const Core::Type& t) { return Core::showType(t); },
        [&] (const Core::Expr* e) { return e->toString(ctx); }
      }, ctx[*opt]));
      result.tokens.emplace_back(x);
      auto it = defMap.find(name);
      if (it != defMap.end()) result.tokens.back().defPos = it->second;
      return Var{ makeExprLoc(x, Core::Expr::FREE, opt.value()) };
    }
    throw AnalysisErrorException(x, "Undefined identifier: " + name);
  });
  // `addRule`: uses implicit collector
  // Rule: `[var] ::= <op-l-paren>[expr]<op-r-paren>`
  // Collector: constructs a `Var` object from `OpLParen`, `Expr` and `OpRParen`
  parenRule =
  addRule([]     (OpLParen, Expr&& e, OpRParen) -> Var { return { e.e }; });
  addRule([]     (Var&& var)                    -> Vars { return { { var.e } }; });
  addRule([]     (Vars&& vars, Var&& var)       -> Vars { vars.es.push_back(var.e); return vars; });
  addRuleFor<Expr, Vars>([this] (const ParseTree* x) {
    auto vars = getChild<Vars>(x, 0);
    if (vars.es.size() < 1) throw Core::Unreachable();
    Core::Expr* res = vars.es[0];
    vars.es.erase(vars.es.begin());
    if (!vars.es.empty()) {
      if (res->tag == Core::Expr::VAR) res->appendChildren(vars.es);
      else throw AnalysisErrorException(x, "Invalid function application");
    }
    return Expr{ res };
  }, makePrec(1.000, false));

  addRule([this] (ConstTrue)                            -> Expr { return { makeExpr(Core::Expr::TRUE) }; },
          makePrec(1.000, false));
  addRule([this] (ConstFalse)                           -> Expr { return { makeExpr(Core::Expr::FALSE) }; },
          makePrec(1.000, false));
  addRule([this] (ConstEquals, Expr&& lhs, Expr&& rhs)  -> Expr { return { makeExpr(Core::Expr::FREE, ctx.equals, vector<Core::Expr*>{ lhs.e, rhs.e }) }; },
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

  addRuleFor<Expr, Quantifier, NewVars, OpComma, Expr>
  ([this] (const ParseTree* x) {
    auto quantifier = getChild<Quantifier>(x, 0);
    auto names = getChild<NewVars>(x, 1).names;
    for (auto& name: names) {
      boundVars.emplace_back(name, Core::Type{{ 0, Core::Sort::SVAR }});
      defMap[name] = { x->c->startPos, x->c->s->s->endPos };
    }
    auto e = getChild<Expr>(x, 3).e;
    for (auto it = names.rbegin(); it != names.rend(); it++) {
      string name = *it;
      e = makeExpr(quantifier.tag, name, 0, Core::Sort::SVAR, e);
      boundVars.pop_back();
    }
    return Expr{ e };
  }, makePrec(0.100, false));

  addRuleFor<Expr, Quantifier2, NewArities, OpComma, Expr>
  ([this] (const ParseTree* x) {
    auto quantifier = getChild<Quantifier2>(x, 0);
    auto names = getChild<NewArities>(x, 1).names;
    for (auto& [name, arity]: names) {
      boundVars.emplace_back(name, Core::Type{{ arity, quantifier.sort }});
      defMap[name] = { x->c->startPos, x->c->s->s->endPos };
    }
    auto e = getChild<Expr>(x, 3).e;
    for (auto it = names.rbegin(); it != names.rend(); it++) {
      string name = it->first; unsigned short arity = it->second;
      e = makeExpr(quantifier.tag, name, arity, quantifier.sort, e);
      boundVars.pop_back();
    }
    return Expr{ e };
  }, makePrec(0.050, false));

  addRuleFor<Expr, NewVars, OpVertBar, Expr>
  ([this] (const ParseTree* x) {
    auto names = getChild<NewVars>(x, 0).names;
    for (auto& name: names) {
      boundVars.emplace_back(name, Core::Type{{ 0, Core::Sort::SVAR }});
      defMap[name] = { x->c->startPos, x->c->s->endPos };
    }
    auto e = getChild<Expr>(x, 2).e;
    for (auto it = names.rbegin(); it != names.rend(); it++) {
      string name = *it;
      e = makeExpr(Core::Expr::LAM, name, 0, Core::Sort::SVAR, e);
      boundVars.pop_back();
    }
    return Expr{ e };
  }, makePrec(0.050, false));

  addRuleFor<Proof, Identifier>
  ([this] (const ParseTree* x) {
    string name = getChild<Identifier>(x, 0).name;
    auto opt = ctx.lookup(name);
    if (opt.has_value()) {
      result.hovers.emplace_back(x, "", name + ": " + std::visit(Matcher{
        [&] (const Core::Type& t) { return Core::showType(t); },
        [&] (const Core::Expr* e) { return e->toString(ctx); }
      }, ctx[*opt]));
      result.tokens.emplace_back(x);
      auto it = defMap.find(name);
      if (it != defMap.end()) result.tokens.back().defPos = it->second;
      return Proof{ makeProofLoc(x, opt.value()) };
    }
    throw AnalysisErrorException(x, "Undefined identifier: " + name);
  });
/*
  addRuleFor<Proof, ProofRule>
  ([this] (const ParseTree* x) { return Proof{ makeProofLoc(x, getChild<ProofRule>(x, 0).tag) }; });
  addRuleFor<Proof, ProofRule, Proof>
  ([this] (const ParseTree* x) { return Proof{ makeProofLoc(x, getChild<ProofRule>(x, 0).tag, getChild<Proof>(x, 1).pf) }; });
  addRuleFor<Proof, ProofRule, Proof, Proof>
  ([this] (const ParseTree* x) { return Proof{ makeProofLoc(x, getChild<ProofRule>(x, 0).tag, getChild<Proof>(x, 1).pf, getChild<Proof>(x, 2).pf) }; });
  addRuleFor<Proof, ProofRule, Proof, Proof, Proof>
  ([this] (const ParseTree* x) { return Proof{ makeProofLoc(x, getChild<ProofRule>(x, 0).tag, getChild<Proof>(x, 1).pf, getChild<Proof>(x, 2).pf, getChild<Proof>(x, 3).pf) }; });
  addRule([]     (OpLParen, Proof&& pf, OpRParen) -> Proof { return pf; });
*/

  #undef makeExpr
  #undef makeProof

  addRuleFor<WFE, Expr>
  ([this] (const ParseTree* x) {
    boundVars.clear();
    auto e = getChild<Expr>(x, 0).e;
    try {
      auto t = e->checkType(ctx);
      result.hovers.emplace_back(x, "", e->toString(ctx) + ": " + Core::showType(t));
      // result.info.emplace_back(x, e->toString(ctx) + ": " + Core::showType(t));
      return WFE{ e, t };
    } catch (Core::CheckFailure& ex) {
      throw AnalysisErrorException(x, e->toString(ctx) + ":\n" + ex.what());
    }
  });

  addRuleFor<WFF, WFE>
  ([this] (const ParseTree* x) {
    auto [e, t] = getChild<WFE>(x, 0);
    if (t != Core::TFormula) throw AnalysisErrorException(x, "Expected formula, got type " + Core::showType(t));
    return WFF{ e };
  });

  addRuleFor<WFP, Proof>
  ([this] (const ParseTree* x) {
    auto pf = getChild<Proof>(x, 0).pf;
    try {
      auto e = pf->check(ctx, exprs);
      result.hovers.emplace_back(x, "", string("Proves: ") + e->toString(ctx));
      return WFP{ pf, e };
    } catch (Core::CheckFailure& ex) {
      throw AnalysisErrorException(x, string("Error checking proof:\n") + ex.what());
    }
  });

  addRule([]     (Identifier&& id)                            -> NewVar { return { id.name }; });
  addRule([]     (NewVar&& v)                                 -> NewVars { return { { v.name } }; });
  addRule([]     (NewVars&& vs, OpComma)                      -> NewVars { return vs; });
  addRule([]     (NewVars&& vs, OpComma, NewVar&& v)          -> NewVars { vs.names.push_back(v.name); return vs; });
  addRule([]     (Identifier&& id, OpSlash, Natural&& n)      -> NewArity { return { id.name, static_cast<unsigned short>(n.data) }; });
  addRule([]     (NewArity&& f)                               -> NewArities { return { { { f.name, f.arity } } }; });
  addRule([]     (NewArities&& fs, OpComma)                   -> NewArities { return fs; });
  addRule([]     (NewArities&& fs, OpComma, NewArity&& f)     -> NewArities { fs.names.emplace_back(f.name, f.arity); return fs; });
  addRule([]     (WFF&& e, OptName&& name)                    -> Assumption { return { name.name.value_or(""), e.e }; });
  addRule([]     (Assumption&& a)                             -> Assumptions { return { { { a.name, a.expr } } }; });
  addRule([]     (Assumptions&& as, OpComma)                  -> Assumptions { return as; });
  addRule([]     (Assumptions&& as, OpComma, Assumption&& a)  -> Assumptions { as.as.emplace_back(a.name, a.expr); return as; });
  addRuleFor<Any, KwAny, NewVars>
  ([this] (const ParseTree* x) {
    auto names = getChild<NewVars>(x, 1).names;
    for (auto& name: names) {
      ctx.pushVar(name, Core::Type{{ 0, Core::Sort::SVAR }});
      defMap[name] = { x->startPos, x->endPos };
    }
    scopes.emplace_back(names.size(), 0);
    immediate = true;
    return Any{};
  });
  addRuleFor<AnyFunc, KwAnyFunc, NewArities>
  ([this] (const ParseTree* x) {
    auto fs = getChild<NewArities>(x, 1).names;
    for (auto& [name, arity]: fs) {
      ctx.pushVar(name, Core::Type{{ arity, Core::Sort::SVAR }});
      defMap[name] = { x->startPos, x->endPos };
    }
    scopes.emplace_back(fs.size(), 0);
    immediate = true;
    return AnyFunc{};
  });
  addRuleFor<AnyPred, KwAnyPred, NewArities>
  ([this] (const ParseTree* x) {
    auto ps = getChild<NewArities>(x, 1).names;
    for (auto& [name, arity]: ps) {
      ctx.pushVar(name, Core::Type{{ arity, Core::Sort::SPROP }});
      defMap[name] = { x->startPos, x->endPos };
    }
    scopes.emplace_back(ps.size(), 0);
    immediate = true;
    return AnyPred{};
  });
  addRuleFor<Assume, KwAssume, Assumptions>
  ([this] (const ParseTree* x) {
    auto as = getChild<Assumptions>(x, 1).as;
    for (auto& [name, e]: as) {
      ctx.pushAssumption(name, e);
      defMap[name] = { x->startPos, x->endPos };
    }
    scopes.emplace_back(as.size(), 0);
    immediate = true;
    return Assume{};
  });

  addRule([]     ()                        -> OptRRArrow { return {}; });
  addRule([]     (OpRRArrow)               -> OptRRArrow { return {}; });
  addRule([]     ()                        -> OptProof { return { nullopt }; });
  addRule([]     (KwProof, WFP&& pf)       -> OptProof { return { pf }; });
  addRule([]     ()                        -> OptName { return { nullopt }; });
  addRule([]     (KwName, Identifier&& id) -> OptName { return { id.name }; });
  addRule([]     ()                        -> OptSemicolon { return {}; });
  addRule([]     (OpSemicolon)             -> OptSemicolon { return {}; });
  addRuleFor<Assertion, OptRRArrow, WFF, OptName, OptProof, OptSemicolon>
  ([this] (const ParseTree* x) {
    // TODO: verify or start tableau thread
    auto e = getChild<WFF>(x, 1).e;
    auto name = getChild<OptName>(x, 2).name;
    auto pf = getChild<OptProof>(x, 3).pf;
    if (!pf) {
      result.info.emplace_back(x, "No proof");
      // throw AnalysisErrorException(x, "No proof");
    } else if (/* e &&*/ pf && *pf->e != *e) {
      throw AnalysisErrorException(x, 
          string("Invalid assertion, statement and proof do not match\n")
        + "Statement: " + e->toString(ctx) + "\n" + "Proof: " + pf->e->toString(ctx));
    }
    ctx.addTheorem(name.value_or(""), e);
    defMap[name.value_or("")] = { x->startPos, x->endPos };
    return Assertion{};
  });

  addRuleFor<Def, KwDef, Identifier, OpColonEq, WFE, OptName, OptSemicolon>(
  [this] (const ParseTree* x) {
    auto id = getChild<Identifier>(x, 1);
    auto e = getChild<WFE>(x, 3);
    auto namedef = getChild<OptName>(x, 4);
    Core::Decl::Tag tag;
    if (e.t == Core::TTerm) tag = Core::Decl::FDEF;
    else if (e.t == Core::TFormula) tag = Core::Decl::PDEF;
    else throw AnalysisErrorException(x, "Expected term or formula, got type " + Core::showType(e.t));
    Core::Decl decl(tag, id.name, namedef.name.value_or(""), e.e);
    try {
      decl.check(ctx, exprs);
      defMap[id.name] = { x->startPos, x->endPos };
      defMap[namedef.name.value_or("")] = { x->startPos, x->endPos };
    } catch (Core::CheckFailure& ex) {
      throw AnalysisErrorException(x, e.e->toString(ctx) + ":\n" + ex.what());
    }
    return Def{};
  });

  addRuleFor<List, KwMetaList>
  ([this] (const ParseTree* x) {
    string msg;
    for (size_t i = 0; i < ctx.size(); i++) {
      msg += ctx.nameOf(i) + ": " + std::visit(Matcher{
        [&] (const Core::Type& t) { return Core::showType(t); },
        [&] (const Core::Expr* e) { return e->toString(ctx); }
      }, ctx[i]) + "\n";
    }
    result.info.emplace_back(x, msg);
    return List{};
  });

  addRule([]     (String&& s)                          -> MacroRuleSymbol { return { { true, s.data } }; });
  addRule([]     (Identifier&& s)                      -> MacroRuleSymbol { return { { false, s.name } }; });
  addRule([]     (MacroRuleSymbol&& s)                 -> MacroRule { return { { s.s } }; });
  addRule([]     (MacroRule&& ss, MacroRuleSymbol&& s) -> MacroRule { ss.ss.push_back(s.s); return ss; });
  addRule([]     ()                                    -> OptPrec { return { nullopt }; });
  addRule([]     (KwPrec, Decimal&& d)                 -> OptPrec { return { d.data }; });
  addRule([]     ()                                    -> OptAssoc { return { 0 }; });
  addRule([]     (KwRightmostLongest)                  -> OptAssoc { return { 1 }; });
  addRule([]     (KwRightmostShortest)                 -> OptAssoc { return { -1 }; });
  addRuleFor<MacroDef, KwMetaDef, MacroRule, OpColonEq, Expr, KwName, Identifier, OptPrec, OptAssoc, OptSemicolon>
  ([this] (const ParseTree* x) {
    auto pattern          = getChild<MacroRule> (x, 1).ss;
    string rulename       = getChild<Identifier>(x, 5).name;
    double prec           = getChild<OptPrec>   (x, 6).prec.value_or(0.5);
    bool rightmostLongest = getChild<OptAssoc>  (x, 7).f == 1;
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
    size_t rid = addRuleImpl(SymbolName<Expr>::get(), getSymbol<Expr>(), rhs,
    ([this, term, positions] (const ParseTree* x) {
      std::unordered_map<string, const ParseTree*> mp;
      for (auto& [key, val]: positions) {
        const ParseTree* p = x->c;
        for (size_t i = 0; i < val; i++) p = p->s;
        mp[key] = p;
      }
      ParseTree* transformed = replaceVarsByExprs(term, mp);
      return get<Expr>(transformed);
    }), makePrec(prec, rightmostLongest));
    // Add record
    customParsingRules[rulename] = { rid, words };
    return MacroDef{};
  });
  addRuleFor<MacroUndef, KwMetaUndef, Identifier, OptSemicolon>
  ([this] (const ParseTree* x) {
    string name = getChild<Identifier>(x, 1).name;
    auto it = customParsingRules.find(name);
    if (it == customParsingRules.end()) {
      result.errors.emplace_back(x, "Unknown parsing rule \"" + name + "\"");
    } else {
      parser.rules[it->second.first].active = false;
      for (const string& word: it->second.second) removeWordlikePattern(word);
      customParsingRules.erase(it);
    }
    return MacroUndef{};
  });

  addRule([]     (Assertion)                 -> Decl { return {}; });
  addRule([]     (Assume)                    -> Decl { return {}; });
  addRule([]     (Any)                       -> Decl { return {}; });
  addRule([]     (AnyFunc)                   -> Decl { return {}; });
  addRule([]     (AnyPred)                   -> Decl { return {}; });
  addRule([]     (Def)                       -> Decl { return {}; });
  addRule([]     (Idef)                      -> Decl { return {}; });
  addRule([]     (Undef)                     -> Decl { return {}; });

  addRuleFor<Decl, OpLBrace>
  ([this] (const ParseTree*) {
    if (scopes.empty()) throw Core::Unreachable();
    scopes.back().second++;
    return Decl{};
  });
  addRuleFor<Decl, OpRBrace>
  ([this] (const ParseTree* x) {
    if (scopes.empty()) throw Core::Unreachable();
    if (scopes.size() == 1 && scopes.back().second <= 1) throw AnalysisErrorException(x, "Unexpected closing brace");
    scopes.back().second--;
    return Decl{};
  });

  addRule([]     (List)                      -> Decl { return {}; });
  addRule([]     (MacroDef)                  -> Decl { return {}; });
  addRule([]     (MacroUndef)                -> Decl { return {}; });

  // Ad-hoc fix for the statement-level disambiguation failure case (`any x, y, x = y`)
  // (combine two `Decl`s into one, in order to parse them together...)
  addRuleFor<Decl, Any, OpComma, Assertion>
  ([this] (const ParseTree* x) {
    getChild<Any>(x, 0);
    immediate = false;
    getChild<Assertion>(x, 2);
    return Decl{};
  });
  addRuleFor<Decl, Assume, OpComma, Assertion>
  ([this] (const ParseTree* x) {
    getChild<Assume>(x, 0);
    immediate = false;
    getChild<Assertion>(x, 2);
    return Decl{};
  });

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
      result.errors.push_back(ex);
    }
    if (!immediate) {
      while (!scopes.empty() && scopes.back().second == 0) {
        for (size_t i = 0; i < scopes.back().first; i++) ctx.pop(exprs);
        scopes.pop_back();
      }
    }
  }
}

AnalysisResult Mu::popResults() {
  AnalysisResult res;
  std::swap(result, res);
  return res;
}
