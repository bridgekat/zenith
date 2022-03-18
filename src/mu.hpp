// :: Mu

#ifndef MU_HPP_
#define MU_HPP_

#include "parsing/language.hpp"
#include "core.hpp"


class Mu: public Parsing::Language {
public:
  struct AnalysisInfo {
    size_t startPos, endPos;
    std::string info;
    AnalysisInfo(const Parsing::ParseTree* x, const std::string& s): startPos(x->startPos), endPos(x->endPos), info(s) {}
    AnalysisInfo(size_t startPos, size_t endPos, const std::string& s): startPos(startPos), endPos(endPos), info(s) {}
  };

  struct AnalysisErrorException: public std::runtime_error {
    size_t startPos, endPos;
    AnalysisErrorException(const Parsing::ParseTree* x, const std::string& s): std::runtime_error(s), startPos(x->startPos), endPos(x->endPos) {}
    AnalysisErrorException(size_t startPos, size_t endPos, const std::string& s): std::runtime_error(s), startPos(startPos), endPos(endPos) {}
  };

  Mu();
  void analyze(const std::string& str);
  std::vector<AnalysisInfo> popAnalysisInfo();
  std::vector<AnalysisErrorException> popAnalysisErrors();

private:
  Core::Allocator<Core::Expr> exprs;
  Core::Allocator<Core::Proof> proofs;

  Core::Context ctx;
  size_t op1; // TEMP CODE (for testing infix parsing)
  std::vector<std::string> boundVars;
  std::unordered_map<void*, std::pair<size_t, size_t>> sourceMap;
  std::vector<AnalysisInfo> info;
  std::vector<AnalysisErrorException> errors;

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
