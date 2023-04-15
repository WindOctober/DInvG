#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "llvm/Support/CommandLine.h"

using namespace clang;
using namespace clang::tooling;
using namespace llvm;
using namespace clang::ast_matchers;

static llvm::cl::OptionCategory MyToolCategory("My tool options");

int main(int argc, const char **argv) {
  llvm::Expected<clang::tooling::CommonOptionsParser> OptionsParser=CommonOptionsParser::create(argc, argv, MyToolCategory);
  ClangTool Tool(OptionsParser->getCompilations(),
                 OptionsParser->getSourcePathList());

  MatchFinder Finder;
  Finder.addMatcher(stmt().bind("stmt"), nullptr);

  Tool.run(newFrontendActionFactory(&Finder).get());

  return 0;
}