#ifndef CFGVISITOR_H
#define CFGVISITOR_H

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

extern set<string> Main_Functions;
extern set<string> Visited_Functions;

class CFGVisitor:public RecursiveASTVisitor<CFGVisitor>{
public:
    enum class VisitorState { Collect_All_Function, Main };
    explicit CFGVisitor(ASTContext *context,VisitorState VS):context(context),VS(VS),pp(context->getPrintingPolicy()){}
    
    void error_output(string error){
        outs()<<error<<"\n";
        exit(-1);
    }

    void TraverseCFG(unique_ptr<CFG>& cfg);
    bool VisitCallExpr(CallExpr *CE);
    bool VisitFunctionDecl(FunctionDecl *func);

private:
    ASTContext *context;
    PrintingPolicy pp;
    VisitorState VS;
};

#endif
