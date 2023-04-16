#include"clang/Tooling/CommonOptionsParser.h"
#include"clang/Tooling/Tooling.h"
#include"clang/Frontend/FrontendActions.h"
#include"clang/Frontend/CompilerInstance.h"
#include"clang/AST/ASTContext.h"
#include"clang/AST/ASTConsumer.h"
#include"clang/AST/RecursiveASTVisitor.h"
#include"clang/Analysis/CFG.h"
#include<stack>
#include<set>
using namespace std;
using namespace clang;
using namespace llvm;
using namespace clang::tooling;

class CFGVisitor:public RecursiveASTVisitor<CFGVisitor>{
public:
    explicit CFGVisitor(ASTContext *context):context(context),pp(context->getPrintingPolicy()){}
    void PrintCFG(unique_ptr<CFG>& cfg){
        stack<const CFGBlock*> BlockStack;
        set<const CFGBlock*> Visited;
        BlockStack.push(&cfg->getEntry());
        outs()<<"the entry block of the function is: Basic Block "<<(&cfg->getEntry())->getBlockID()<<"\n";
        outs()<<"the exit block of the function is: Basic Block "<<(&cfg->getExit())->getBlockID()<<"\n";
        while(!BlockStack.empty()){
            const CFGBlock* cur=BlockStack.top();
            BlockStack.pop();
            if (Visited.count(cur)) continue;
            Visited.insert(cur);
            outs()<<"\t BasicBlock:"<<cur->getBlockID()<<"\n";
            if (!cur->empty()){
                for (const auto &element : *cur) {
                    if (const Stmt *stmt = element.castAs<CFGStmt>().getStmt()) {
                        string stmt_str;
                        raw_string_ostream ostream(stmt_str);
                        stmt->printPretty(ostream,nullptr,pp);
                        ostream.flush();
                        outs()<<"\t\t\tStatement type:"<<stmt->getStmtClassName()<<"\n";
                        outs()<<"\t\t\tStatement:"<<stmt_str<<"\n";
                    }
                    if (const clang::Stmt *terminator = cur->getTerminator().getStmt()){
                        std::string condition;
                        llvm::raw_string_ostream ostream(condition);
                        terminator->printPretty(ostream,nullptr,pp);
                        ostream.flush();
                        outs()<<"Conditional jump with condition: "<<condition<<"\n";
                    }
                }
            }
            for(auto it=cur->succ_begin();it!=cur->succ_end();it++){
                const CFGBlock* succ=*it;
                BlockStack.push(succ);
                outs()<<"\t\t\tsucc Basic Block is :"<<succ->getBlockID()<<"\n";
            }
        }
    }
    bool VisitCallExpr(CallExpr *CE) {
        FunctionDecl *callee = CE->getDirectCallee();
        if (callee) {
            auto cfg=CFG::buildCFG(callee,callee->getBody(),context,CFG::BuildOptions());
            outs()<<"CalleeFunction:"<<callee->getNameAsString()<<"\n";
            PrintCFG(cfg);
        }
        return true;
    }
    bool VisitFunctionDecl(FunctionDecl *func) {
        if (func->getNameAsString()=="main") {
            auto cfg=CFG::buildCFG(func,func->getBody(),context,CFG::BuildOptions());
            outs()<< "Function:"<< func->getNameAsString()<<"\n";
            PrintCFG(cfg);
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
    unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &ci,StringRef) {
        return make_unique<CFGASTConsumer>(&ci.getASTContext());
    }
};

static cl::OptionCategory ToolCategory("CFG Tool Options");

int main(int argc,const char **argv) {
    auto optionsParser=CommonOptionsParser::create(argc,argv,ToolCategory);
    ClangTool tool(optionsParser->getCompilations(),optionsParser->getSourcePathList());
    return tool.run(newFrontendActionFactory<CFGFrontendAction>().get());
}
