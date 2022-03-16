#ifndef APIMU_HPP_
#define APIMU_HPP_

#include "../language.hpp"


namespace Parsing {

  class ApiMuLanguage: public Language {
  public:

    // Terminal symbols

    struct Blank {};
    struct LineComment {};
    struct BlockComment {};
    struct Directive {};

    struct Natural { uint32_t data; };
    struct String { string data; };

    struct OpComma {};
    struct OpSemicolon {};
    struct OpLBrace {};
    struct OpRBrace {};
    struct OpRRArrow {};
    struct OpSlash {};

    struct KwAny {};
    struct KwAnyFunc {};
    struct KwAnyPred {};
    struct KwAssume {};
    struct KwName {};
    struct KwProof {};

    struct Operator { string name; };
    struct Identifier { string name; };

    // Nonterminal symbols

    struct Decls {};
    struct Decl {};
    struct Block {};

    struct Assertion {};
    struct OptName {};
    struct OptProof {};

    struct Assume {};
    struct Assumptions {};
    struct Assumption {};

    struct Any {};
    struct Vars {};
    struct Var {};

    struct AnyFunc {};
    struct Funcs {};
    struct Func {};

    struct AnyPred {};
    struct Preds {};
    struct Pred {};

    struct Expr {};
    struct Idents {};
    struct Ident {};

    ApiMuLanguage();

  private:
    
  };

}

#endif // APIMU_HPP_
