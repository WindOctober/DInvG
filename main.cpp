#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Analysis/CFG.h"

using namespace clang;
using namespace llvm;
using namespace clang::tooling;



class CFGVisitor : public RecursiveASTVisitor<CFGVisitor> {
public:
    explicit CFGVisitor(ASTContext *context) : context(context), pp(context->getPrintingPolicy()) {}
    bool VisitFunctionDecl(FunctionDecl *func) {
        if (func->hasBody()) {
            auto cfg = CFG::buildCFG(func, func->getBody(), context, CFG::BuildOptions());
            outs() << "Function: " << func->getNameInfo().getAsString() << "\n";
            for (const auto *block : *cfg) {
                outs() << "  BasicBlock: " << block->getBlockID() << "\n";
                
                outs() << "    Statements:\n";
                for (const auto &elem : *block) {
                    if (const Stmt *stmt = elem.castAs<CFGStmt>().getStmt()) {
                        std::string stmt_str;
                        raw_string_ostream ostream(stmt_str);
                        stmt->printPretty(ostream, nullptr, pp);
                        ostream.flush();
                        outs() << "      " << stmt_str << "\n";
                    }
                }

                // 输出基本块的前驱
                outs() << "    Predecessors:\n";
                for (const CFGBlock::AdjacentBlock &pred : block->preds()) {
                    if (pred.isReachable()) {
                        outs() << "      BasicBlock: " << pred->getBlockID() << "\n";
                    }
                }

                // 输出基本块的后继
                outs() << "    Successors:\n";
                for (const CFGBlock::AdjacentBlock &succ : block->succs()) {
                    if (succ.isReachable()) {
                        outs() << "      BasicBlock: " << succ->getBlockID() << "\n";
                    }
                }
            }
        }
        return true;
    }

private:
    ASTContext *context;
    PrintingPolicy pp;
};

class CFGASTConsumer : public ASTConsumer {
public:
    explicit CFGASTConsumer(ASTContext *context) : visitor(context) {}

    virtual void HandleTranslationUnit(ASTContext &context) {
        visitor.TraverseDecl(context.getTranslationUnitDecl());
    }

private:
    CFGVisitor visitor;
};


class CFGFrontendAction : public ASTFrontendAction {
protected:
    std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &ci, StringRef) {
        return std::make_unique<CFGASTConsumer>(&ci.getASTContext());
    }
};

static cl::OptionCategory ToolCategory("CFG Tool Options");

int main(int argc, const char **argv) {
    auto optionsParser=CommonOptionsParser::create(argc, argv, ToolCategory);
    ClangTool tool(optionsParser->getCompilations(), optionsParser->getSourcePathList());
    return tool.run(newFrontendActionFactory<CFGFrontendAction>().get());
}
