// :: Mu

#ifndef MU_HPP_
#define MU_HPP_

#include "parsing/language.hpp"
#include "core.hpp"

struct AnalyzeErrorException: public std::runtime_error {
  size_t startPos, endPos;
  explicit AnalyzeErrorException(const Parsing::ParseTree* x, const std::string& s = ""):
    std::runtime_error(s), startPos(x->startPos), endPos(x->endPos) {}
};

class Mu: public Parsing::Language {
public:
  Mu();
  void analyze(const std::string& str);

  // TEMP CODE
  std::vector<Parsing::ParseErrorException> popLexerErrors() { return NFALexer::popErrors(); }

private:
  Core::Allocator<Core::Expr> exprs;
  Core::Allocator<Core::Proof> proofs;

  Core::Context ctx;
  size_t op1; // TEMP CODE (for testing infix parsing)
  std::vector<std::string> boundVars;
  std::unordered_map<void*, std::pair<size_t, size_t>> sourceMap;

  template <typename ...Ts>
  Core::Expr* makeExprLoc(const Parsing::ParseTree* x, const Ts&... args) {
    Core::Expr* res = exprs.pushBack(Core::Expr(args...));
    sourceMap[res] = { x->startPos, x->endPos };
    return res;
  }

  template <typename ...Ts>
  Core::Proof* makeProofLoc(const Parsing::ParseTree* x, const Ts&... args) {
    Core::Proof* res = proofs.pushBack(Core::Proof(args...));
    sourceMap[res] = { x->startPos, x->endPos };
    return res;
  }
};

#endif // MU_HPP_
