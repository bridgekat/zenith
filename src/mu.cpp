#include "mu.hpp"
#include <optional>

using std::string;
using std::vector;
using std::pair, std::make_pair;
using std::optional, std::make_optional, std::nullopt;
using Parsing::ParseTree;


// ===================
// Symbol declarations
// ===================

#define symbol(T) struct T; template <> struct Parsing::SymbolName<T> { static const char* get() { return #T; } }; struct T

// Terminal symbols

symbol(Blank) {};
symbol(LineComment) {};
symbol(BlockComment) {};
symbol(Directive) {};

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

symbol(KwAny) {};
symbol(KwAnyFunc) {};
symbol(KwAnyPred) {};
symbol(KwAssume) {};
symbol(KwName) {};
symbol(KwProof) {};

symbol(Infix80) { string name; };
symbol(Infix60) { string name; };
symbol(Infix40) { string name; };
symbol(Prefix30) { string name; };
symbol(Infix20) { string name; };

symbol(Binder) { string name; };
symbol(Identifier) { string name; };

// Nonterminal symbols

symbol(Error) {};

symbol(Var) { Core::Expr* e; };
symbol(Vars) { vector<Core::Expr*> es; };
symbol(Term100) { Core::Expr* e; };
symbol(Term80) { Core::Expr* e; };
symbol(Term60) { Core::Expr* e; };
symbol(Term40) { Core::Expr* e; };
symbol(Term30) { Core::Expr* e; };
symbol(Term20) { Core::Expr* e; };
symbol(Term) { Core::Expr* e; };

symbol(Expr) { Core::Expr* e; };                   // Assumed to be verified
symbol(Proof) { Core::Expr* e; Core::Proof* pf; }; // Assumed to be verified

symbol(NewVar) { string name; };
symbol(NewVars) { vector<string> names; };
symbol(Any) {};

symbol(NewFunc) { string name; unsigned short arity; };
symbol(NewFuncs) { vector<pair<string, unsigned short>> fs; };
symbol(AnyFunc) {};

symbol(NewPred) { string name; unsigned short arity; };
symbol(NewPreds) { vector<pair<string, unsigned short>> ps; };
symbol(AnyPred) {};

symbol(Assumption) { string name; Core::Expr* expr; };
symbol(Assumptions) { vector<pair<string, Core::Expr*>> as; };
symbol(Assume) {};

symbol(OptProof) { optional<Core::Proof*> proof; };
symbol(OptName) { optional<string> name; };
symbol(Assertion) {};

symbol(Decl) {};
symbol(Block) {};
symbol(Decls) {};

#undef symbol


// ====================================
// Patterns, rules and semantic actions
// ====================================

Mu::Mu(): exprs(), proofs(), ctx(), op1(ctx.pushVar("*", Core::Type{{ 2, Core::Sort::SVAR }})), boundVars(), sourceMap() {

  // Terminal symbols

  #define trivial(T) [] (const string&) -> T { return {}; }

  addPattern(trivial(Blank), star(ch({ ' ', '\t', '\n', '\v', '\f', '\r' })), true);
  addPattern(trivial(LineComment), concat(word("//"), star(except({ '\r', '\n' }))), true);
  addPattern(trivial(BlockComment),
    concat(word("/*"),
      star(concat(star(except({ '*' })), plus(ch({ '*' })), except({ '/' }))),
                  star(except({ '*' })), plus(ch({ '*' })), ch({ '/' })), true);
  addPattern(trivial(Directive),
    concat(ch({ '\r', '\n' }), star(ch({ ' ', '\t', '\n', '\v', '\f', '\r' })),
      ch({ '#' }), star(except({ '\r', '\n' }))), true);

  addPattern([] (const string& lexeme) -> Natural { return { static_cast<uint32_t>(std::stoi(lexeme)) }; },
    alt({ star(range('0', '9')),
          concat(ch({ '0' }), ch({ 'x', 'X' }), star(alt({ range('0', '9'), range('a', 'f'), range('A', 'F') }))) }));
  addPattern([] (const string& lexeme) -> String { return { lexeme.substr(1, lexeme.size() - 1) }; },
    concat(ch({ '"' }), star(alt({ except({ '"', '\\' }), concat(ch({ '\\' }), ch({ '"', '\\' })) })), ch({ '"' })));

  addPattern(trivial(OpComma),     word(","));
  addPattern(trivial(OpSemicolon), word(";"));
  addPattern(trivial(OpLParen),    word("("));
  addPattern(trivial(OpRParen),    word(")"));
  addPattern(trivial(OpLBrace),    word("{"));
  addPattern(trivial(OpRBrace),    word("}"));
  addPattern(trivial(OpRRArrow),   word("=>"));
  addPattern(trivial(OpSlash),     word("/"));

  addPattern(trivial(KwAny),     word("any"));
  addPattern(trivial(KwAnyFunc), word("anyfunc"));
  addPattern(trivial(KwAnyPred), word("anypred"));
  addPattern(trivial(KwAssume),  word("assume"));
  addPattern(trivial(KwName),    word("name"));
  addPattern(trivial(KwProof),   word("proof"));

  addPattern([] (const string& lexeme) -> Infix80 { return { lexeme }; }, ch({ '*', '\\', '%', '^', }));
  addPattern([] (const string& lexeme) -> Infix60 { return { lexeme }; }, ch({ '+', '-' }));
  addPattern([] (const string& lexeme) -> Infix40 { return { lexeme }; }, alt({ ch({ '=', '<', '>' }), word("!="), word(">="), word("<=") }));
  addPattern([] (const string& lexeme) -> Infix20 { return { lexeme }; },
    alt({ word("and"), word("or"), word("implies"), word("iff"), word("->"), word("<->") }));
  addPattern([] (const string& lexeme) -> Prefix30 { return { lexeme }; },
    alt({ word("not") }));
  addPattern([] (const string& lexeme) -> Binder { return { lexeme }; },
    alt({ word("forall"), word("exists"), word("unique"), word("forallfunc"), word("forallpred") }));
  addPattern([] (const string& lexeme) -> Identifier { return { lexeme }; },
    concat(
      alt({ range('a', 'z'), range('A', 'Z'), ch({ '_', '`' }), utf8segment() }),
      star(alt({ range('a', 'z'), range('A', 'Z'), range('0', '9'), ch({ '_', '`', '\'', '.' }), utf8segment() }))));

  #undef trivial

  // Nonterminal symbols

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

  // TODO: binders

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
  addRule([this] (Term80&& lhs, Infix80&&, Term100&& rhs)   -> Term80 { return { makeExpr(Core::Expr::FREE, op1, vector<Core::Expr*>{ lhs.e, rhs.e }) }; }); // TODO: lookup table
  addRule([]     (Term80&& t)                               -> Term60 { return { t.e }; });
  addRule([this] (Term60&& lhs, Infix60&&, Term80&& rhs)    -> Term60 { return { makeExpr(Core::Expr::FREE, op1, vector<Core::Expr*>{ lhs.e, rhs.e }) }; });
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
  addRule([]     (Term20&& t)                               -> Term { return { t.e }; });
  addRule([]     (OpLParen, Term&& t, OpRParen)             -> Var { return { t.e }; });

  addRuleFor<Expr, Term>([this] (const ParseTree* x) -> Expr {
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
  addRuleFor<Any, KwAny, NewVars, Decl>([this] (const ParseTree* x) -> Any {
    auto names = getChild<NewVars>(x, 1).names;
    for (auto& name: names) ctx.pushVar(name, Core::Type{{ 0, Core::Sort::SVAR }});
    getChild<Decl>(x, 2);
    for (size_t i = 0; i < names.size(); i++) ctx.pop(exprs);
    return {};
  });

  addRule([]     (Identifier&& id, OpSlash, Natural&& n) -> NewFunc { return { id.name, static_cast<unsigned short>(n.data) }; });
  addRule([]     (NewFunc&& f)                           -> NewFuncs { return { { { f.name, f.arity } } }; });
  addRule([]     (NewFuncs&& fs, OpComma)                -> NewFuncs { return fs; });
  addRule([]     (NewFuncs&& fs, OpComma, NewFunc&& f)   -> NewFuncs { fs.fs.emplace_back(f.name, f.arity); return fs; });
  addRuleFor<AnyFunc, KwAnyFunc, NewFuncs, Decl>([this] (const ParseTree* x) -> AnyFunc {
    auto fs = getChild<NewFuncs>(x, 1).fs;
    for (auto& [name, arity]: fs) ctx.pushVar(name, Core::Type{{ arity, Core::Sort::SVAR }});
    getChild<Decl>(x, 2);
    for (size_t i = 0; i < fs.size(); i++) ctx.pop(exprs);
    return {};
  });

  addRule([]     (Identifier&& id, OpSlash, Natural&& n) -> NewPred { return { id.name, static_cast<unsigned short>(n.data) }; });
  addRule([]     (NewPred&& p)                           -> NewPreds { return { { { p.name, p.arity } } }; });
  addRule([]     (NewPreds&& ps, OpComma)                -> NewPreds { return ps; });
  addRule([]     (NewPreds&& ps, OpComma, NewPred&& p)   -> NewPreds { ps.ps.emplace_back(p.name, p.arity); return ps; });
  addRuleFor<AnyPred, KwAnyPred, NewPreds, Decl>([this] (const ParseTree* x) -> AnyPred {
    auto ps = getChild<NewPreds>(x, 1).ps;
    for (auto& [name, arity]: ps) ctx.pushVar(name, Core::Type{{ arity, Core::Sort::SPROP }});
    getChild<Decl>(x, 2);
    for (size_t i = 0; i < ps.size(); i++) ctx.pop(exprs);
    return {};
  });

  addRule([]     (Expr&& e, OptName&& name)                  -> Assumption { return { name.name.value_or(""), e.e }; });
  addRule([]     (Assumption&& a)                            -> Assumptions { return { { { a.name, a.expr } } }; });
  addRule([]     (Assumptions&& as, OpComma)                 -> Assumptions { return as; });
  addRule([]     (Assumptions&& as, OpComma, Assumption&& a) -> Assumptions { as.as.emplace_back(a.name, a.expr); return as; });
  addRuleFor<Assume, KwAssume, Assumptions, Decl>([this] (const ParseTree* x) -> Assume {
    auto as = getChild<Assumptions>(x, 1).as;
    for (auto& [name, e]: as) ctx.pushAssumption(name, e);
    getChild<Decl>(x, 2);
    for (size_t i = 0; i < as.size(); i++) ctx.pop(exprs);
    return {};
  });

  addRule([]     ()                                                      -> OptProof { return { nullopt }; });
  addRule([]     (KwProof, Proof&& pf)                                   -> OptProof { return { pf.pf }; });
  addRule([]     ()                                                      -> OptName { return { nullopt }; });
  addRule([]     (KwName, Identifier&& id)                               -> OptName { return { id.name }; });
  addRule([this] (OpRRArrow, Expr&&, OptName&&, OptProof&&, OpSemicolon) -> Assertion {
    // TODO: verify or start tableau thread
    return {};
  });

  // To generate verifiable `Decl`s, complete these actions
  // Currently omitted for clarity
  addRule([]     (Block)                     -> Decl { return {}; });
  addRule([]     (Assertion)                 -> Decl { return {}; });
  addRule([]     (Assume)                    -> Decl { return {}; });
  addRule([]     (Any)                       -> Decl { return {}; });
  addRule([]     (AnyFunc)                   -> Decl { return {}; });
  addRule([]     (AnyPred)                   -> Decl { return {}; });
  addRule([]     (OpLBrace, Decls, OpRBrace) -> Block { return {}; });
  addRule([]     ()                          -> Decls { return {}; });
  addRuleFor<Decls, Decls, Decl>([this] (const ParseTree* x) -> Decls {
    getChild<Decls>(x, 0);
    try { getChild<Decl>(x, 1); } catch (AnalysisErrorException& ex) { errors.push_back(ex); }
    return {};
  });

  // Error recovery rules (TODO: add more?)
  addRule([]     (OpLBrace, Error, OpRBrace)     -> Block { return {}; });
  addRule([]     (OpRRArrow, Error, OpSemicolon) -> Assertion { return {}; });
  addRule([]     (KwAssume, Error, Decl)         -> Assume { return {}; });
  addRule([]     (KwAny, Error, Decl)            -> Any { return {}; });
  addRule([]     (KwAnyFunc, Error, Decl)        -> AnyFunc { return {}; });
  addRule([]     (KwAnyPred, Error, Decl)        -> AnyPred { return {}; });
  addRule([]     (Error)                         -> Decl { return {}; });

  #undef expr
  #undef proof

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
  Language::setAsErrorSymbol<Error>();
  Language::parse<Decls>(str);
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
