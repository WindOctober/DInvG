#include<stddef.h>
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
#include<vector>

using namespace std;
using namespace clang;
using namespace llvm;
using namespace clang::tooling;

set<string> Main_Functions;
set<string> Visited_Functions;
class CFGVisitor:public RecursiveASTVisitor<CFGVisitor>{
public:
    enum class VisitorState { Collect_All_Function, Main };
    explicit CFGVisitor(ASTContext *context,VisitorState VS):context(context),VS(VS),pp(context->getPrintingPolicy()){}
    
    void error_output(string error){
        outs()<<error<<"\n";
        exit(-1);
    }

    void PrintCFG(unique_ptr<CFG>& cfg){
        stack<const CFGBlock*> BlockStack;
        set<const CFGBlock*> Visited;
        BlockStack.push(&cfg->getEntry());
        outs()<<"the entry block of the function is: Basic Block "<<(&cfg->getEntry())->getBlockID()<<"\n";
        outs()<<"the exit block of the function is: Basic Block "<<(&cfg->getExit())->getBlockID()<<"\n";
        while(!BlockStack.empty()){
            const CFGBlock* cur=BlockStack.top();
            BlockStack.pop();
            if (!cur) return;
            const clang::Stmt *terminator;
            terminator = cur->getTerminator().getStmt();
            // outs()<<"\t\t\tStatement type:"<<terminator->getStmtClass()<<"\n";
            if (Visited.count(cur)) continue;
            Visited.insert(cur);
            outs()<<"\tBasicBlock:"<<cur->getBlockID()<<"\n";
        
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
                }
                
                if (terminator){
                    string condition;
                    raw_string_ostream ostream(condition);
                    terminator->printPretty(ostream,nullptr,pp);
                    ostream.flush();
                    outs()<<"\t\t\tConditional jump with condition: "<<terminator->getStmtClassName()<<"\n";
                }
            }
            for(auto it=cur->succ_begin();it && it!=cur->succ_end();it++){
                const CFGBlock* succ=*it;
                BlockStack.push(*it);
                if (!terminator)
                    outs()<<"\t\t\tsucc Basic Block is :"<<succ->getBlockID()<<"\n";
                else{
                    if (clang::isa<clang::ForStmt>(terminator)){
                        const CFGBlock* Body_Block=*it;
                        it++;
                        if (!(*it)){
                            outs()<<"\t\t\tsucc Exit Loop Block is :"<<Body_Block->getBlockID()<<'\n';
                            continue;
                        }
                        const CFGBlock* Exit_Block=*it;
                        if (it==cur->succ_end()){
                            outs()<<"\t\t\tsucc Exit Loop Block is :"<<Body_Block->getBlockID()<<'\n';
                        }
                        else{
                            outs()<<"\t\t\tsucc Loop body Block is :"<<Body_Block->getBlockID()<<'\n';
                            outs()<<"\t\t\tsucc Exit Loop Block is :"<<Exit_Block->getBlockID()<<'\n';
                            BlockStack.push(Exit_Block);
                        }
                    }
                    else if (clang::isa<clang::IfStmt>(terminator)){
                        if (!succ){
                            error_output("\tunspecified mode for if statement. As there exists no then branch of if statement.");
                        }
                        const CFGBlock* Then_Block=*it;
                        it++;
                        if (!(*it)){
                            outs()<<"\t\t\tsucc Then Block is :"<<Then_Block->getBlockID()<<'\n';
                            continue;
                        }
                        const CFGBlock* Else_Block=*it;
                        outs()<<"\t\t\tsucc Then Block is :"<<Then_Block->getBlockID()<<'\n';
                        if (it!=cur->succ_end()){
                            outs()<<"\t\t\tsucc Else Block is :"<<Else_Block->getBlockID()<<'\n';
                            BlockStack.push(Else_Block);
                        }
                    }
                    else if (clang::isa<clang::WhileStmt>(terminator)){
                        const CFGBlock* Body_Block=*it;
                        it++;
                        if (!(*it)){
                            outs()<<"\t\t\tsucc Exit Loop Block is :"<<Body_Block->getBlockID()<<'\n';
                            continue;
                        }
                        const CFGBlock* Exit_Block=*it;
                        if (it==cur->succ_end()){
                            outs()<<"\t\t\tsucc Exit Loop Block is :"<<Body_Block->getBlockID()<<'\n';
                        }
                        else{
                            outs()<<"\t\t\tsucc Loop body Block is :"<<Body_Block->getBlockID()<<'\n';
                            outs()<<"\t\t\tsucc Exit Loop Block is :"<<Exit_Block->getBlockID()<<'\n';
                            BlockStack.push(Exit_Block);
                        }
                    }
                    else if (clang::isa<clang::ReturnStmt>(terminator)){
                        outs()<<"\t\t\tsucc Return Block is :"<<succ->getBlockID()<<"\n";
                    }
                }
            }
        }
    }
    bool VisitCallExpr(CallExpr *CE) {
        if (VS!=VisitorState::Main) return true;
        FunctionDecl *callee = CE->getDirectCallee();
        if (callee && Visited_Functions.count(callee->getNameAsString())==0) {
            SourceManager &SM = context->getSourceManager();
            if (!SM.isInMainFile(callee->getLocation())) return true;
            Visited_Functions.insert(callee->getNameAsString());
            auto cfg=CFG::buildCFG(callee,callee->getBody(),context,CFG::BuildOptions());
            outs()<<"CalleeFunction:"<<callee->getNameAsString()<<"\n";
            PrintCFG(cfg);
        }
        return true;
    }
    bool VisitFunctionDecl(FunctionDecl *func) {
        SourceManager &SM = context->getSourceManager();
        if (!SM.isInMainFile(func->getLocation())) return true;
        if (VS==VisitorState::Collect_All_Function){
            Main_Functions.insert(func->getNameAsString());
            return true;
        }
        if (func->getNameAsString()=="main" || Main_Functions.count("main")==0) {
            auto cfg=CFG::buildCFG(func,func->getBody(),context,CFG::BuildOptions());
            outs()<<"Function:"<< func->getNameAsString()<<"\n";
            PrintCFG(cfg);
        }
        return true;
    }

private:
    ASTContext *context;
    PrintingPolicy pp;
    VisitorState VS;
};

class CFGASTConsumer : public ASTConsumer {
public:
    explicit CFGASTConsumer(ASTContext *context) : visitor(context,CFGVisitor::VisitorState::Main) {}

    virtual void HandleTranslationUnit(ASTContext &context) {
        CFGVisitor Function_Visitor(&context,CFGVisitor::VisitorState::Collect_All_Function);
        Function_Visitor.TraverseDecl(context.getTranslationUnitDecl());
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
cl::opt<string> InputFilename(cl::Positional, cl::desc("<input file>"), cl::Required,cl::cat(ToolCategory));
cl::opt<bool> EnableFeature("enable-feature", cl::desc("Enable specific feature"), cl::init(false));

int main(int argc,const char **argv) {
    cl::HideUnrelatedOptions(ToolCategory);
    cl::ParseCommandLineOptions(argc, argv);

    vector<string> sources;
    sources.push_back(InputFilename.getValue());

    string errorMsg;
    int remainingArgc = argc;
    auto compilationDB = FixedCompilationDatabase::loadFromCommandLine(remainingArgc, argv, errorMsg);
    if (!compilationDB) {
        errs() << "Warning: Using default compilation options.\n";
        SmallString<256> currentDir;
        sys::fs::current_path(currentDir);
        compilationDB = std::make_unique<FixedCompilationDatabase>(Twine(currentDir), ArrayRef<std::string>());
    }

    ClangTool tool(*compilationDB, sources);
    return tool.run(newFrontendActionFactory<CFGFrontendAction>().get());
}
