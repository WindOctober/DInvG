#ifndef CFGVISITOR_H
#define CFGVISITOR_H

#include"clang/Tooling/CommonOptionsParser.h"
#include"clang/Tooling/Tooling.h"
#include"clang/Frontend/FrontendActions.h"
#include"clang/Frontend/CompilerInstance.h"
#include"clang/AST/ASTContext.h"
#include"clang/AST/ASTConsumer.h"
#include"clang/AST/RecursiveASTVisitor.h"
#include"clang/Analysis/CFG.h"
#include<stack>
#include<ppl.hh>
#include"TransitionSystem.hpp"
#include"Variable.hpp"
    
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
    explicit CFGVisitor(ASTContext *context,VisitorState VS):context(context),VS(VS),pp(context->getPrintingPolicy()),Transystem(context){}
    enum class ErrorType {FloatVarError,UnexpectedTypeError,CFGInitError,VarDeclUnFoundError,CalleeUnFoundError};
    void error_output(string error){
        outs()<<error<<"\n";
        exit(-1);
    }


    bool VisitCallExpr(CallExpr *CE);
    bool VisitFunctionDecl(FunctionDecl *func);
    void PrintStmtInfo(Stmt* stmt);

private:

    void DealWithStmt(Stmt* stmt,int left,int right);

    void DealWithVarDecl(VarDecl* stmt,int left,int right);
    void DealWithFunctionDecl(FunctionDecl* stmt,int left,int right);
    void Terminate_errors(enum ErrorType Errors);
    ASTContext *context;
    PrintingPolicy pp;
    VisitorState VS;
    TransitionSystem Transystem;
};

#endif
