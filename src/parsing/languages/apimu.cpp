#include "apimu.hpp"


namespace Parsing {

  #define demangle(T) template <> struct SymbolName<ApiMuLanguage::T> { static const char* get() { return #T; } };

  // Terminal symbols

  demangle(Blank); demangle(LineComment); demangle(BlockComment); demangle(Directive);
  demangle(Natural); demangle(String);
  demangle(OpComma); demangle(OpSemicolon); demangle(OpLBrace); demangle(OpRBrace); demangle(OpRRArrow); demangle(OpSlash);
  demangle(KwAny); demangle(KwAnyFunc); demangle(KwAnyPred); demangle(KwAssume); demangle(KwName); demangle(KwProof);
  demangle(Operator); demangle(Identifier);

  // Nonterminal symbols

  demangle(Decls); demangle(Decl); demangle(Block);
  demangle(Assertion); demangle(OptName); demangle(OptProof);
  demangle(Assume); demangle(Assumptions); demangle(Assumption);
  demangle(Any); demangle(Vars); demangle(Var);
  demangle(AnyFunc); demangle(Funcs); demangle(Func);
  demangle(AnyPred); demangle(Preds); demangle(Pred);
  demangle(Expr); demangle(Idents); demangle(Ident);

  #undef demangle

  ApiMuLanguage::ApiMuLanguage() {

    // Terminal symbols

    #define trivial(T) [] (const string&) { return T{}; }

    addPattern(trivial(Blank), star(ch({ ' ', '\t', '\n', '\v', '\f', '\r' })), true);
    addPattern(trivial(LineComment), concat(word("//"), star(except({ '\r', '\n' }))), true);
    addPattern(trivial(BlockComment),
      concat(word("/*"),
        star(concat(star(except({ '*' })), plus(ch({ '*' })), except({ '/' }))),
                    star(except({ '*' })), plus(ch({ '*' })), ch({ '/' })), true);
    addPattern(trivial(Directive), concat(ch({ '#' }), star(except({ '\r', '\n' }))), true);

    addPattern([] (const string& lexeme) { return Natural { static_cast<uint32_t>(std::stoi(lexeme)) }; },
      alt({ star(range('0', '9')),
            concat(ch({ '0' }), ch({ 'x', 'X' }), star(alt({ range('0', '9'), range('a', 'f'), range('A', 'F') }))) }));
    addPattern([] (const string& lexeme) { return String { lexeme.substr(1, lexeme.size() - 1) }; },
      concat(ch({ '"' }), star(alt({ except({ '"', '\\' }), concat(ch({ '\\' }), ch({ '"', '\\' })) })), ch({ '"' })));

    addPattern(trivial(OpComma), word(","));
    addPattern(trivial(OpSemicolon), word(";"));
    addPattern(trivial(OpLBrace), word("{"));
    addPattern(trivial(OpRBrace), word("}"));
    addPattern(trivial(OpRRArrow), word("=>"));
    addPattern(trivial(OpSlash), word("/"));

    addPattern(trivial(KwAny), word("any"));
    addPattern(trivial(KwAnyFunc), word("anyfunc"));
    addPattern(trivial(KwAnyPred), word("anypred"));
    addPattern(trivial(KwAssume), word("assume"));
    addPattern(trivial(KwName), word("name"));
    addPattern(trivial(KwProof), word("proof"));

    addPattern([] (const string& lexeme) { return Operator { lexeme }; },
      alt({ ch({ '=', '+', '-', '*', '\\', '%', '&', '(', ')', ':', '?', '[', ']', '^', '|', '<', '>' }),
            word("->"), word("<->"), word("↑") }));
    addPattern([] (const string& lexeme) { return Identifier { lexeme }; },
      concat(
        alt({ range('a', 'z'), range('A', 'Z'), ch({ '_', '`' }), utf8segment() }),
        star(alt({ range('a', 'z'), range('A', 'Z'), range('0', '9'), ch({ '_', '`', '\'', '.' }), utf8segment() }))));

    #undef trivial

    // Nonterminal symbols

    #define trivial(T, ...) [] (__VA_ARGS__) { return T{}; }

    addRule(trivial(Decls));
    addRule(trivial(Decls, Decls, Decl));

    addRule(trivial(Decl, Block));
    addRule(trivial(Decl, Directive));
    addRule(trivial(Decl, Assertion));
    addRule(trivial(Decl, Assume));
    addRule(trivial(Decl, Any));
    addRule(trivial(Decl, AnyFunc));
    addRule(trivial(Decl, AnyPred));

    addRule(trivial(Block, OpLBrace, Decls, OpRBrace));

    addRule(trivial(Assertion, OpRRArrow, Expr, OptName, OptProof, OpSemicolon));
    addRule(trivial(OptName));
    addRule(trivial(OptName, KwName, Identifier));
    addRule(trivial(OptProof));
    addRule(trivial(OptProof, KwProof, Expr));

    addRule(trivial(Assume, KwAssume, Assumptions, Decl));
    addRule(trivial(Assumptions, Assumption));
    addRule(trivial(Assumptions, Assumptions, OpComma, Assumption));
    addRule(trivial(Assumptions, Assumptions, OpComma)); // Optional commas anywhere!
    addRule(trivial(Assumption, Expr, OptName));

    addRule(trivial(Any, KwAny, Vars, Decl));
    addRule(trivial(Vars, Var));
    addRule(trivial(Vars, Vars, OpComma, Var));
    addRule(trivial(Vars, Vars, OpComma)); // Optional commas anywhere!
    addRule(trivial(Var, Identifier));

    addRule(trivial(AnyFunc, KwAnyFunc, Funcs, Decl));
    addRule(trivial(Funcs, Func));
    addRule(trivial(Funcs, Funcs, OpComma, Func));
    addRule(trivial(Funcs, Funcs, OpComma));
    addRule(trivial(Func, Identifier, OpSlash, Natural));

    addRule(trivial(AnyPred, KwAnyPred, Preds, Decl));
    addRule(trivial(Preds, Pred));
    addRule(trivial(Preds, Preds, OpComma, Pred));
    addRule(trivial(Preds, Preds, OpComma));
    addRule(trivial(Pred, Identifier, OpSlash, Natural));

    addRule(trivial(Expr, Idents));
    addRule(trivial(Idents, Ident));
    addRule(trivial(Idents, Idents, Ident));
    addRule(trivial(Ident, Operator));
    addRule(trivial(Ident, Identifier));

    #undef trivial

  }

}
