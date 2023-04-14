#include "clang/Analysis/CFG.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "llvm/Support/CommandLine.h"

// using namespace clang::tooling;
// using namespace clang;

int main(int argc, const char **argv) {
  // CommonOptionsParser OptionsParser(argc, argv);
  // ClangTool Tool(OptionsParser.getCompilations(),
  //                OptionsParser.getSourcePathList());

  // for (const auto &Source : Tool.getFiles()) {
  //   ASTUnit ast = ASTUnit::LoadFromASTFile(Source->getName());
  //   if (!ast) {
  //     llvm::errs() << "Failed to load AST for " << Source->getName() << "\n";
  //     continue;
  //   }

  //   SourceManager &SM = ast->getSourceManager();
  //   const FunctionDecl *FD = ast->getASTContext().getTranslationUnitDecl();
  //   if (!FD) {
  //     llvm::errs() << "Failed to get translation unit for " << Source->getName() << "\n";
  //     continue;
  //   }

  //   CFG::BuildOptions BO;
  //   BO.setAllAlwaysAdd();
  //   CFG *cfg = CFG::buildCFG(FD, FD->getBody(), &ast->getASTContext(), BO);

  //   cfg->dump(LangOptions(), true);
  // }

  return 0;
}

