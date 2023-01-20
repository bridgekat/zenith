#include "evaluator.hpp"
// TEMP CODE?
#include <fstream>
#include <iostream>
#include <limits>

using std::string;
using std::vector;
using std::pair;
using std::optional, std::get_if;
using Parsing::AutomatonBuilder, Parsing::GrammarBuilder;

namespace Eval {

  auto Evaluator::parseNextStatement() -> bool {
    assert(bool(parser));
    return parser->advance();
    // std::cout << parser->showStates(symbolNames) << std::endl;
  }

  auto Evaluator::evalParsedStatement() -> Tree* {
    auto e = resolve(); // std::cout << e->toString() << std::endl;
    e = expand(e);
    std::cout << e->toString() << std::endl;
    e = eval(globalEnv, e);
    return e;
  }

  auto Evaluator::popParsingErrors() -> vector<ParsingError> {
    auto res = vector<ParsingError>();
    // See:
    // https://stackoverflow.com/questions/30448182/is-it-safe-to-use-a-c11-range-based-for-loop-with-an-rvalue-range-init
    /*
    for (auto const& e: lexer.popErrors()) {
      res.emplace_back("Parsing error, unexpected characters: " + e.lexeme, e.begin, e.end);
    }
    for (auto const& e: parser.popErrors()) {
      string s = "Parsing error, expected one of: ";
      for (Symbol sym: e.expected) s += "<" + symbolNames[sym] + ">, ";
      if (e.got) s += "got token <" + symbolNames[*e.got] + ">";
      else s += "but reached the end of file";
      res.emplace_back(s, e.begin, e.end);
    }
    */
    return res;
  }

  // Match an Tree against another Tree (pattern)
  // See: https://github.com/digama0/mm0/blob/master/mm0-hs/mm1.md#syntax-forms
  // (Continuation, `__k`, `and`, `or`, `not` and `pred?` patterns are not implemented)
  auto Evaluator::match(Tree* e, Tree* pat, Tree*& env, bool quoteMode) -> bool {
    if (auto const& sym = get_if<Symbol>(pat); sym && !quoteMode) {
      if (sym->val != "_") env = extend(env, sym->val, e);
      return true;
    }
    if (auto const& cons = get_if<Cons>(pat)) {
      auto const& [h, t] = *cons;
      if (auto const& sym = get_if<Symbol>(h)) {
        if (sym->val == "quote" && !quoteMode) return match(e, expect<Cons>(t).head, env, true);   // Enter quote mode
        if (sym->val == "unquote" && quoteMode) return match(e, expect<Cons>(t).head, env, false); // Leave quote mode
        if (sym->val == "...") return get_if<Nil>(e) || get_if<Cons>(e);
      }
      auto const& econs = get_if<Cons>(e);
      return econs && match(econs->head, h, env, quoteMode) && match(econs->tail, t, env, quoteMode);
    }
    return *e == *pat;
  }

  auto stringToCharVec(string const& s) -> vector<Parsing::Char> {
    auto res = vector<Parsing::Char>();
    for (auto const c: s) res.push_back(static_cast<Parsing::Char>(c));
    return res;
  }

  auto Evaluator::treePattern(AutomatonBuilder& builder, Tree* e) -> AutomatonBuilder::Subgraph {
    auto const& [tag, t] = expect<Cons>(e);
    auto const& stag = expect<Symbol>(tag).val;
    if (stag == "empty") return builder.empty();
    if (stag == "any") return builder.any();
    if (stag == "utf8seg") return builder.utf8segment();
    if (stag == "char") return builder.chars(stringToCharVec(expect<String>(expect<Cons>(t).head).val));
    if (stag == "except") return builder.except(stringToCharVec(expect<String>(expect<Cons>(t).head).val));
    if (stag == "range") {
      auto const& [lbound, u] = expect<Cons>(t);
      auto const& [ubound, _] = expect<Cons>(u);
      return builder.range(
        static_cast<Parsing::Char>(expect<Nat64>(lbound).val),
        static_cast<Parsing::Char>(expect<Nat64>(ubound).val)
      );
    }
    if (stag == "word") return builder.word(stringToCharVec(expect<String>(expect<Cons>(t).head).val));
    if (stag == "alt") return builder.alt(listPatterns(builder, t));
    if (stag == "concat") return builder.concat(listPatterns(builder, t));
    if (stag == "opt") return builder.opt(treePattern(builder, expect<Cons>(t).head));
    if (stag == "star") return builder.star(treePattern(builder, expect<Cons>(t).head));
    if (stag == "plus") return builder.plus(treePattern(builder, expect<Cons>(t).head));
    unimplemented;
  }

  auto Evaluator::listPatterns(AutomatonBuilder& builder, Tree* e) -> vector<AutomatonBuilder::Subgraph> {
    auto res = vector<AutomatonBuilder::Subgraph>();
    for (auto it = get_if<Cons>(e); it; it = get_if<Cons>(it->tail)) { res.push_back(treePattern(builder, it->head)); }
    return res;
  }

  auto Evaluator::listSymbols(Tree* e) -> vector<pair<Parsing::Symbol, Parsing::Precedence>> {
    auto res = vector<pair<Parsing::Symbol, Parsing::Precedence>>();
    for (auto it = get_if<Cons>(e); it; it = get_if<Cons>(it->tail)) {
      auto const& [sym, t] = expect<Cons>(it->head);
      auto const& [prec, _] = expect<Cons>(t);
      res.emplace_back(symbol(expect<Symbol>(sym).val), static_cast<Parsing::Precedence>(expect<Nat64>(prec).val));
    }
    return res;
  }

  // TODO: handle exceptions, refactor
  auto Evaluator::setSyntax(Tree* p, Tree* r) -> void {
    auto automatonBuilder = AutomatonBuilder();
    auto grammarBuilder = GrammarBuilder();

    symbolNames.clear();
    nameSymbols.clear();
    ruleNames.clear();
    nameRules.clear();

    patterns = p;
    rules = r;

    // Add ignored and starting symbols.
    symbolNames.emplace_back("_");
    grammarBuilder.withIgnoredSymbol(ignoredSymbol);
    symbolNames.emplace_back("_");
    grammarBuilder.withStartSymbol(startSymbol);

    // Add patterns.
    for (auto it = get_if<Cons>(patterns); it; it = get_if<Cons>(it->tail)) {
      auto const& [lhs, t] = expect<Cons>(it->head);
      auto const& [rhs, _] = expect<Cons>(t);
      auto const& sname = expect<Symbol>(lhs).val;
      auto const sid = sname == "_" ? ignoredSymbol : symbol(sname);
      automatonBuilder.withPattern(sid, treePattern(automatonBuilder, rhs));
    }

    // Add rules.
    for (auto it = get_if<Cons>(rules); it; it = get_if<Cons>(it->tail)) {
      auto const& [name, t] = expect<Cons>(it->head);
      auto const& [lhs, u] = expect<Cons>(t);
      auto const& [rhs, _1] = expect<Cons>(u);
      auto const& [sym, v] = expect<Cons>(lhs);
      auto const& [prec, _2] = expect<Cons>(v);
      auto const& sname = expect<Symbol>(sym).val;
      auto const& rname = expect<Symbol>(name).val;
      auto const sid = sname == "_" ? startSymbol : symbol(sname);
      auto const sprec = static_cast<Parsing::Precedence>(expect<Nat64>(prec).val);
      grammarBuilder.withRule(std::pair(sid, sprec), listSymbols(rhs));
      ruleNames.push_back(rname);
    }

    // Finalise.
    automaton = std::make_unique<Parsing::DFA const>(automatonBuilder.makeDFA(true));
    grammar = std::make_unique<Parsing::Grammar const>(grammarBuilder.make());
    // Rebuild dependents if needed.
    if (lexer || parser) {
      if (lookaheads) lookaheads->invalidate();
      if (buffer) {
        lexer = std::make_unique<Parsing::Lexer>(*automaton, *buffer);
        lookaheads = std::make_unique<Parsing::LookaheadBuffer<std::optional<Parsing::Token>>>(*lexer);
        parser = std::make_unique<Parsing::Parser>(*grammar, *lookaheads);
      } else {
        lexer.reset();
        lookaheads.reset();
        parser.reset();
      }
    }
  }

#define cons       pool.emplace
#define nil        nil
#define sym(s)     pool.emplace(Symbol{s})
#define str(s)     pool.emplace(String{s})
#define nat(n)     pool.emplace(Nat64{n})
#define boolean(b) pool.emplace(Bool{b})
#define unit       unit
#define list(...)  makeList({__VA_ARGS__})

  // Initialize with built-in patterns, rules, forms and procedures
  // See: https://github.com/digama0/mm0/blob/master/mm0-hs/mm1.md#syntax-forms
  // See: https://github.com/digama0/mm0/blob/master/mm0-hs/mm1.md#Prim-functions
  Evaluator::Evaluator() {
    // Commonly used constants
    // auto const& nzero  = pool.emplace(Nat64{ 0 });
    // auto const& sempty = pool.emplace(String{ "" });
    auto const& btrue = pool.emplace(Bool{true});
    auto const& bfalse = pool.emplace(Bool{false});

    // =========================
    // Default syntax and macros
    // =========================

#define symbol(s)            list(sym(s), nat(0))
#define pattern(lhs, pat)    list(sym(lhs), pat)
#define rule(name, lhs, rhs) list(sym(name), lhs, rhs)
#define empty                list(sym("empty"))
#define any                  list(sym("any"))
#define utf8seg              list(sym("utf8seg"))
#define chars(s)             list(sym("char"), str(s))
#define except(s)            list(sym("except"), str(s))
#define range(l, u)          list(sym("range"), nat(l), nat(u))
#define word(s)              list(sym("word"), str(s))
#define alt(...)             list(sym("alt"), __VA_ARGS__)
#define concat(...)          list(sym("concat"), __VA_ARGS__)
#define opt(pat)             list(sym("opt"), pat)
#define star(pat)            list(sym("star"), pat)
#define plus(pat)            list(sym("plus"), pat)

    Tree* defaultPatterns = list(
      pattern("_", star(chars(" \f\n\r\t\v"))),               // Blank
      pattern("_", concat(word("//"), star(except("\n\r")))), // Line comment
      pattern(                                                // Block comment
        "_",
        concat(
          word("/*"),
          star(concat(star(except("*")), plus(chars("*")), except("/"))),
          star(except("*")),
          plus(chars("*")),
          chars("/")
        )
      ),
      pattern(
        "symbol",
        concat(
          alt(range('a', 'z'), range('A', 'Z'), chars("_'"), utf8seg),
          star(alt(range('a', 'z'), range('A', 'Z'), range('0', '9'), chars("_'"), utf8seg))
        )
      ),
      pattern(
        "nat64",
        alt(
          plus(range('0', '9')),
          concat(chars("0"), chars("xX"), plus(alt(range('0', '9'), range('a', 'f'), range('A', 'F'))))
        )
      ),
      pattern(
        "string",
        concat(chars("\""), star(alt(except("\\\""), concat(chars("\\"), chars("\\\"abfnrtv")))), chars("\""))
      ),
      pattern("left_paren", word("(")),
      pattern("right_paren", word(")")),
      pattern("period", word(".")),
      pattern("quote", word("`")),
      pattern("comma", word(","))
    );

    Tree* defaultRules = list(
      rule("symbol'", symbol("tree"), list(symbol("symbol"))),
      rule("nat64'", symbol("tree"), list(symbol("nat64"))),
      rule("string'", symbol("tree"), list(symbol("string"))),
      rule("nil'", symbol("list"), list()),
      rule("cons'", symbol("list"), list(symbol("tree"), symbol("list"))),
      rule("period'", symbol("list"), list(symbol("tree"), symbol("period"), symbol("tree"))),
      rule("quote'", symbol("tree"), list(symbol("quote"), symbol("tree"))),
      rule("unquote'", symbol("tree"), list(symbol("comma"), symbol("tree"))),
      rule("tree'", symbol("tree"), list(symbol("left_paren"), symbol("list"), symbol("right_paren"))),
      rule("id'", symbol("_"), list(symbol("tree")))
    );

    setSyntax(defaultPatterns, defaultRules);
    addMacro("symbol'", Closure{globalEnv, list(sym("s")), list(list(sym("string_symbol"), sym("s")))});
    addMacro("nat64'", Closure{globalEnv, list(sym("n")), list(list(sym("string_nat64"), sym("n")))});
    addMacro(
      "string'",
      Closure{
        globalEnv,
        list(sym("s")),
        list(list(
          sym("string_unescape"),
          list(sym("string_substr"), sym("s"), nat(1), list(sym("sub"), list(sym("string_length"), sym("s")), nat(2)))
        ))}
    );
    addMacro("nil'", Closure{globalEnv, list(), list(list(sym("nil")))});
    addMacro("cons'", Closure{globalEnv, list(sym("l"), sym("r")), list(list(sym("cons"), sym("l"), sym("r")))});
    addMacro("id'", Closure{globalEnv, list(sym("l")), list(sym("l"))});
    addMacro(
      "period'",
      Closure{globalEnv, list(sym("l"), sym("_"), sym("r")), list(list(sym("cons"), sym("l"), sym("r")))}
    );
    addMacro(
      "quote'",
      Closure{
        globalEnv,
        list(sym("_"), sym("l")),
        list(list(sym("list"), list(sym("string_symbol"), str("quote")), sym("l")))}
    );
    addMacro(
      "unquote'",
      Closure{
        globalEnv,
        list(sym("_"), sym("l")),
        list(list(sym("list"), list(sym("string_symbol"), str("unquote")), sym("l")))}
    );
    addMacro("tree'", Closure{globalEnv, list(sym("_"), sym("l"), sym("_")), list(sym("l"))});

#undef syncat
#undef pattern
#undef rule
#undef empty
#undef any
#undef utf8seg
#undef chars
#undef except
#undef range
#undef word
#undef alt
#undef concat
#undef opt
#undef star
#undef plus
#undef list

    // ===============
    // Primitive forms
    // ===============

    // [√] Introduction rule for `Closure`
    addPrimitive("lambda", false, [this](Tree* env, Tree* e) -> Result {
      auto const& [formal, es] = expect<Cons>(e);
      return pool.emplace(Closure{env, formal, es});
    });

    // [√] Elimination rule for `Bool`
    addPrimitive("cond", false, [this](Tree* env, Tree* e) -> Result {
      auto const& [test, t] = expect<Cons>(e);
      auto const& [iftrue, u] = expect<Cons>(t);
      auto const& iffalse = (get_if<Cons>(u) ? get_if<Cons>(u)->head : unit);
      bool result = expect<Bool>(eval(env, test)).val;
      return {env, result ? iftrue : iffalse};
    });

    // [√] Introduction rule for sealed `Tree`
    addPrimitive("quote", false, [this](Tree* env, Tree* e) -> Result {
      return quasiquote(env, expect<Cons>(e).head);
    });
    addPrimitive("unquote", false, [this](Tree* env, Tree* e) -> Result { return eval(env, expect<Cons>(e).head); });

    // [√] Elimination rule for sealed `Tree`
    addPrimitive("match", false, [this](Tree* env, Tree* e) -> Result {
      auto const& [head, t] = expect<Cons>(e);
      auto const& [clauses, _1] = expect<Cons>(t);
      auto const& target = eval(env, head);
      for (auto it = get_if<Cons>(clauses); it; it = get_if<Cons>(it->tail)) {
        auto const& [pat, u] = expect<Cons>(it->head);
        auto newEnv = env;
        if (match(target, pat, newEnv)) {
          auto const& [expr, _2] = expect<Cons>(u);
          return {newEnv, expr};
        }
      }
      // All failed, throw exception
      auto msg = string("nonexhaustive patterns: { ");
      auto first = true;
      for (auto it = get_if<Cons>(clauses); it; it = get_if<Cons>(it->tail)) {
        auto const& [pat, _2] = expect<Cons>(it->head);
        if (!first) msg += ", ";
        first = false;
        msg += pat->toString();
      }
      msg += " } ?= " + target->toString();
      throw PartialEvalError(msg, clauses);
    });

    // [√] Currently we don't have a `let`, and this is just a synonym of `let*`...
    addPrimitive("let", false, [this](Tree* env, Tree* e) -> Result {
      auto const& [defs, es] = expect<Cons>(e);
      for (auto it = get_if<Cons>(defs); it; it = get_if<Cons>(it->tail)) {
        auto const& [lhs, t] = expect<Cons>(it->head);
        auto const& [rhs, _] = expect<Cons>(t);
        env = extend(env, expect<Symbol>(lhs).val, eval(env, rhs));
      }
      return {env, beginList(env, es)};
    });

    // [√] Currently we don't have a `letrec`, and this is just a synonym of `letrec*`...
    addPrimitive("letrec", false, [this](Tree* env, Tree* e) -> Result {
      auto const& [defs, es] = expect<Cons>(e);
      // Add #unit (placeholder) bindings.
      auto refs = vector<Tree**>();
      for (auto it = get_if<Cons>(defs); it; it = get_if<Cons>(it->tail)) {
        auto const& [lhs, _] = expect<Cons>(it->head);
        env = extend(env, expect<Symbol>(lhs).val, unit);
        // Will always succeed due to the recent `extend`.
        refs.push_back(&get_if<Cons>(get_if<Cons>(get_if<Cons>(env)->head)->tail)->head);
      }
      // Sequentially evaluate and assign.
      auto i = 0_z;
      for (auto it = get_if<Cons>(defs); it; it = get_if<Cons>(it->tail)) {
        auto const& [lhs, t] = expect<Cons>(it->head);
        auto const& [rhs, _] = expect<Cons>(t);
        *refs[i++] = eval(env, rhs);
      }
      return {env, beginList(env, es)};
    });

    // [√] Global definitions will become effective only on the curr statement...
    // For local definitions, use `letrec*`.
    addPrimitive("define", false, [this](Tree* env, Tree* e) -> Result {
      auto const& [lhs, t] = expect<Cons>(e);
      auto const& [rhs, _] = expect<Cons>(t);
      globalEnv = extend(globalEnv, expect<Symbol>(lhs).val, eval(env, rhs));
      return unit;
    });

    // [?]
    addPrimitive("define_macro", false, [this](Tree* env, Tree* e) -> Result {
      auto const& [lhs, t] = expect<Cons>(e);
      auto const& [rhs, _] = expect<Cons>(t);
      addMacro(expect<Symbol>(lhs).val, expect<Closure>(eval(env, rhs)));
      return unit;
    });

    // [√] This modifies nodes reachable through `env` (which prevents making `Tree*` into const pointers)
    // Ignores more arguments
    addPrimitive("set", false, [this](Tree* env, Tree* e) -> Result {
      auto const& [lhs, t] = expect<Cons>(e);
      auto const& [rhs, _] = expect<Cons>(t);
      auto const value = eval(env, rhs);
      auto const s = expect<Symbol>(lhs).val;
      for (auto it = get_if<Cons>(env); it; it = get_if<Cons>(it->tail))
        if (auto const& u = get_if<Cons>(it->head))
          if (auto const& v = get_if<Cons>(u->tail))
            if (auto const& sym = get_if<Symbol>(u->head); sym && sym->val == s) {
              v->head = value;
              return unit;
            }
      // Not found, throw exception
      throw PartialEvalError("unbound symbol \"" + s + "\"", lhs);
    });

    // [√]
    addPrimitive("begin", false, [this](Tree* env, Tree* e) -> Result { return {env, beginList(env, e)}; });

    // ====================
    // Primitive procedures
    // ====================

    // [√]
    addPrimitive("eval", true, [](Tree* env, Tree* e) -> Result {
      auto const& [h, t] = expect<Cons>(e);
      if (auto const& tcons = get_if<Cons>(t)) env = tcons->head;
      return {env, h}; // Let it restart and evaluate
    });
    addPrimitive("env", true, [](Tree* env, Tree*) -> Result { return env; });
    addPrimitive("get_syntax", true, [this](Tree*, Tree*) -> Result { return cons(patterns, cons(rules, nil)); });
    addPrimitive("set_syntax", true, [this](Tree*, Tree* e) -> Result {
      auto const& [p, t] = expect<Cons>(e);
      auto const& [r, _] = expect<Cons>(t);
      setSyntax(p, r);
      return unit;
    });
    addPrimitive("get_global_env", true, [this](Tree*, Tree*) -> Result { return globalEnv; });
    addPrimitive("set_global_env", true, [this](Tree*, Tree* e) -> Result {
      globalEnv = expect<Cons>(e).head;
      return unit;
    });

    // [√] In principle these can be implemented using patterns and `quote`s,
    // but making them into primitives will make things run faster.
    addPrimitive("nil", true, [this](Tree*, Tree*) -> Result { return nil; });
    addPrimitive("cons", true, [this](Tree*, Tree* e) -> Result {
      auto const& [lhs, t] = expect<Cons>(e);
      auto const& [rhs, _] = expect<Cons>(t);
      return cons(lhs, rhs);
    });
    addPrimitive("list", true, [](Tree*, Tree* e) -> Result { return e; });
    addPrimitive("id", true, [](Tree*, Tree* e) -> Result { return expect<Cons>(e).head; });

    // [√] String functions
    addPrimitive("string_symbol", true, [this](Tree*, Tree* e) -> Result {
      return sym(expect<String>(expect<Cons>(e).head).val);
    });
    addPrimitive("string_nat64", true, [this](Tree*, Tree* e) -> Result {
      return nat(std::stoull(expect<String>(expect<Cons>(e).head).val, nullptr, 0));
    });
    addPrimitive("string_escape", true, [this](Tree*, Tree* e) -> Result {
      return str(Tree::escapeString(expect<String>(expect<Cons>(e).head).val));
    });
    addPrimitive("string_unescape", true, [this](Tree*, Tree* e) -> Result {
      return str(Tree::unescapeString(expect<String>(expect<Cons>(e).head).val));
    });
    addPrimitive("string_length", true, [this](Tree*, Tree* e) -> Result {
      return nat(expect<String>(expect<Cons>(e).head).val.size());
    });
    addPrimitive("string_char", true, [this](Tree*, Tree* e) -> Result {
      auto const& [lhs, t] = expect<Cons>(e);
      auto const& [rhs, _] = expect<Cons>(t);
      auto const& sv = expect<String>(lhs).val;
      auto const iv = expect<Nat64>(rhs).val;
      if (iv >= sv.size()) throw PartialEvalError("Index " + std::to_string(iv) + " out of range", rhs);
      return nat(static_cast<unsigned char>(sv[iv]));
    });
    addPrimitive("char_string", true, [this](Tree*, Tree* e) -> Result {
      auto const& [chr, _] = expect<Cons>(e);
      auto const cv = expect<Nat64>(chr).val;
      if (cv > std::numeric_limits<unsigned char>::max())
        throw PartialEvalError("Character code " + std::to_string(cv) + " out of range", chr);
      return str(string(1, static_cast<char>(cv)));
    });
    addPrimitive("string_concat", true, [this](Tree*, Tree* e) -> Result {
      auto const& [lhs, t] = expect<Cons>(e);
      auto const& [rhs, _] = expect<Cons>(t);
      return str(expect<String>(lhs).val + expect<String>(rhs).val);
    });
    addPrimitive("string_substr", true, [this](Tree*, Tree* e) -> Result {
      auto const& [s, t] = expect<Cons>(e);
      auto const& [pos, u] = expect<Cons>(t);
      auto const& [len, _] = expect<Cons>(u);
      auto const& sv = expect<String>(s).val;
      auto posv = expect<Nat64>(pos).val;
      if (posv > sv.size()) posv = sv.size();
      return str(sv.substr(posv, expect<Nat64>(len).val));
    });
    addPrimitive("string_eq", true, [this](Tree*, Tree* e) -> Result {
      auto const& [lhs, t] = expect<Cons>(e);
      auto const& [rhs, _] = expect<Cons>(t);
      return boolean(expect<String>(lhs).val == expect<String>(rhs).val);
    });

// [√]
#define unary(T, name, op)                                    \
  addPrimitive(name, true, [this](Tree*, Tree* e) -> Result { \
    auto const& [lhs, _] = expect<Cons>(e);                   \
    return pool.emplace(T{op(expect<T>(lhs).val)});           \
  })
#define binary(T, name, op)                                           \
  addPrimitive(name, true, [this](Tree*, Tree* e) -> Result {         \
    auto const& [lhs, t] = expect<Cons>(e);                           \
    auto const& [rhs, _] = expect<Cons>(t);                           \
    return pool.emplace(T{expect<T>(lhs).val op expect<T>(rhs).val}); \
  })
#define binpred(T, name, op)                                            \
  addPrimitive(name, true, [btrue, bfalse](Tree*, Tree* e) -> Result {  \
    auto const& [lhs, t] = expect<Cons>(e);                             \
    auto const& [rhs, _] = expect<Cons>(t);                             \
    return (expect<T>(lhs).val op expect<T>(rhs).val) ? btrue : bfalse; \
  })

    unary(Nat64, "minus", 0 -);
    binary(Nat64, "add", +);
    binary(Nat64, "sub", -);
    binary(Nat64, "mul", *);
    binary(Nat64, "div", /);
    binary(Nat64, "mod", %);
    binpred(Nat64, "le", <=);
    binpred(Nat64, "lt", <);
    binpred(Nat64, "ge", >=);
    binpred(Nat64, "gt", >);
    binpred(Nat64, "eq", ==);
    binpred(Nat64, "neq", !=);
    unary(Bool, "not", !);
    binary(Bool, "and", &&);
    binary(Bool, "or", ||);
    binary(Bool, "implies", <=);
    binary(Bool, "iff", ==);

#undef unary
#undef binary
#undef binpred

    // [√] For debugging?
    addPrimitive("print", true, [this](Tree*, Tree* e) -> Result {
      return pool.emplace(String{expect<Cons>(e).head->toString()});
    });

    // [?] TODO: output to ostream
    addPrimitive("display", true, [this](Tree*, Tree* e) -> Result {
      auto const& [head, tail] = expect<Cons>(e);
      std::cout << expect<String>(head).val << std::endl;
      return unit;
    });
    addPrimitive("debug_save_file", true, [this](Tree*, Tree* e) -> Result {
      auto const& [lhs, t] = expect<Cons>(e);
      auto const& [rhs, _] = expect<Cons>(t);
      auto out = std::ofstream(expect<String>(lhs).val);
      if (!out.is_open()) throw PartialEvalError("Could not open file", lhs);
      out << expect<String>(rhs).val << std::endl;
      return unit;
    });
  }

  // Evaluator entries are stored as lists of two elements.
  auto Evaluator::extend(Tree* env, std::string const& s, Tree* e) -> Tree* {
    return cons(cons(sym(s), cons(e, nil)), env);
  }

  auto Evaluator::lookup(Tree* env, std::string const& s) -> Tree* {
    for (auto it = get_if<Cons>(env); it; it = get_if<Cons>(it->tail)) {
      if (auto const& curr = get_if<Cons>(it->head)) {
        auto const& lhs = curr->head;
        if (auto const& t = get_if<Cons>(curr->tail)) {
          auto const& rhs = t->head;
          if (auto const& sym = get_if<Symbol>(lhs); sym && sym->val == s) return get_if<Unit>(rhs) ? nullptr : rhs;
        }
      }
    }
    return nullptr;
  }

  auto Evaluator::resolve(Parsing::Node const* node, vector<Tree*> const& tails, size_t maxDepth) -> vector<Tree*> {
    if (maxDepth == 0) return {};
    auto const& [state, _, links] = *node;
    auto res = vector<Tree*>();
    if (state.progress == 0) {
      // Whole rule completed.
      for (auto const r: tails) res.push_back(cons(sym(ruleNames[state.rule]), r));
    } else {
      // One step to left.
      for (auto const& [prevLink, childLink]: links) {
        auto const child = std::visit(
          Matcher{
            [&](Parsing::Node const* node) { return resolve(node, {nil}, maxDepth - 1); },
            [&](Parsing::Token const* tok) { return vector<Tree*>(1, str(std::string(tok->lexeme))); },
          },
          childLink
        );
        auto prod = vector<Tree*>();
        for (auto const c: child)
          for (auto const r: tails) prod.push_back(cons(c, r));
        auto const& final = resolve(prevLink, prod, maxDepth);
        for (auto const f: final) res.push_back(f);
      }
    }
    return res;
  }

  auto Evaluator::resolve(size_t maxDepth) -> Tree* {
    assert(grammar && parser);
    auto const& pos = parser->tokens().size();
    auto const& nodes = parser->nodes();
    assert(pos < nodes.size());
    auto all = vector<Tree*>();
    for (auto const& node: nodes[pos]) {
      auto const& [state, _, links] = node;
      auto const& [lhs, rhs] = grammar->rules[state.rule];
      if (state.begin == 0 && lhs.first == startSymbol && state.progress == rhs.size()) {
        auto const& final = resolve(&node, {nil}, maxDepth);
        for (auto const f: final) all.push_back(f);
      }
    }
    if (all.empty()) {
      // Failed to resolve (possibly due to excessive depth or infinite expansion).
      unimplemented;
    }
    if (all.size() > 1) {
      // Ambiguous.
      for (auto const& parse: all) std::cout << parse->toString() << std::endl;
      unimplemented;
    }
    // Mid: all.size() == 1
    return all[0];
  }

#undef cons
#undef nil
#undef sym
#undef str
#undef nat
#undef boolean
#undef unit

  // TODO: custom expansion order
  auto Evaluator::expand(Tree* e) -> Tree* {
    if (get_if<Cons>(e)) {
      // Non-empty lists: expand all macros, from inside out
      try {
        e = expandList(e);
        auto const& [head, tail] = expect<Cons>(e);
        if (auto const& sym = get_if<Symbol>(head)) {
          auto const& it = nameMacros.find(sym->val);
          if (it != nameMacros.end()) {
            auto const& cl = macros[it->second];
            auto env = cl.env;
            if (!match(tail, cl.formal, env))
              throw EvalError("pattern matching failed: " + cl.formal->toString() + " ?= " + tail->toString(), tail, e);
            return eval(env, beginList(env, cl.es));
          }
        }
        return e;

      } catch (PartialEvalError& ex) {
        // "Decorate" partial exceptions with more context, and rethrow a (complete) exception
        throw EvalError(ex.what(), ex.at, e);
      }

    } else {
      // Everything else: expands to itself
      return e;
    }
  }

  // Expands elements in a list
  auto Evaluator::expandList(Tree* e) -> Tree* {
    if (get_if<Nil>(e)) return e;
    else if (auto const& econs = get_if<Cons>(e)) {
      auto const& [head, tail] = *econs;
      auto const& ehead = expand(head);
      auto const& etail = expandList(tail);
      return (ehead == head && etail == tail) ? e : pool.emplace(ehead, etail);
    }
    return expand(e);
  }

  auto Evaluator::eval(Tree* env, Tree* e) -> Tree* {
    while (true) {
      // Evaluate current `e` under current `env`

      if (auto const& sym = get_if<Symbol>(e)) {
        // Symbols: evaluate to their bound values
        if (auto const& val = lookup(env, sym->val)) return val;
        if (auto const& it = namePrims.find(sym->val); it != namePrims.end()) return pool.emplace(Prim{it->second});
        throw PartialEvalError("unbound symbol \"" + sym->val + "\"", e);

      } else if (auto const& econs = get_if<Cons>(e)) {
        // Non-empty lists: evaluate as function application
        try {
          auto const& [head, tail] = *econs;
          auto const& ehead = eval(env, head);

          if (auto const& prim = get_if<Prim>(ehead)) {
            // Primitive function application
            auto const& [evalParams, f] = prims[prim->id];
            auto const& res = f(env, evalParams ? evalList(env, tail) : tail);
            // No tail call, return
            if (!res.env) return res.e;
            // Tail call
            env = res.env;
            e = res.e;
            continue;
          }

          if (auto const& cl = get_if<Closure>(ehead)) {
            // Lambda function application
            auto const& params = evalList(env, tail);
            // Evaluate body as tail call
            env = cl->env;
            if (!match(params, cl->formal, env))
              throw EvalError(
                "pattern matching failed: " + cl->formal->toString() + " ?= " + params->toString(),
                tail,
                e
              );
            e = beginList(env, cl->es);
            continue;
          }

          throw EvalError("head element " + ehead->toString() + " is not a function", head, e);

        } catch (PartialEvalError& ex) {
          // "Decorate" partial exceptions with more context, and rethrow a (complete) exception
          throw EvalError(ex.what(), ex.at, e);
        }

      } else {
        // Everything else: evaluates to itself
        return e;
      }
    }
  }

  // Evaluates elements in a list (often used as parameters)
  auto Evaluator::evalList(Tree* env, Tree* e) -> Tree* {
    if (get_if<Nil>(e)) return e;
    else if (auto const& econs = get_if<Cons>(e)) {
      auto const& [head, tail] = *econs;
      auto const& ehead = eval(env, head);
      auto const& etail = evalList(env, tail);
      return (ehead == head && etail == tail) ? e : pool.emplace(ehead, etail);
    }
    return eval(env, e);
  }

  // Executes elements in a list, except the last one (for tail call optimization)
  // Returns the last one unevaluated, or `#unit` if list is empty
  auto Evaluator::beginList(Tree* env, Tree* e) -> Tree* {
    for (auto it = get_if<Cons>(e); it; it = get_if<Cons>(it->tail)) {
      auto const& [head, tail] = *it;
      if (!get_if<Cons>(tail)) {
        expect<Nil>(tail);
        return head;
      }
      eval(env, head);
    }
    expect<Nil>(e);
    return unit;
  }

  // Evaluates a quasiquoted list
  auto Evaluator::quasiquote(Tree* env, Tree* e) -> Tree* {
    if (auto const& econs = get_if<Cons>(e)) {
      auto const& [head, tail] = *econs;
      if (*head == Tree(Symbol{"unquote"})) return eval(env, expect<Cons>(tail).head);
      auto const& ehead = quasiquote(env, head);
      auto const& etail = quasiquote(env, tail);
      return (ehead == head && etail == tail) ? e : pool.emplace(ehead, etail);
    }
    return e;
  }
}
