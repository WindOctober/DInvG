#ifndef INV_DNFEXPR
#define INV_DNFEXPR
#include"clang/AST/ASTContext.h"
#include"clang/AST/ASTConsumer.h"
#include"clang/AST/RecursiveASTVisitor.h"
#include"clang/Analysis/CFG.h"
#include<vector>
using namespace clang;

enum SExprType{
    
};

class DExpr{
public:
    DExpr();
    DExpr(Stmt init);
    
private:
    struct Term{
        bool primed=false;
        string var;  
    };
    struct SubExpr{
        enum SExprType type;
        vector<Term> terms;
    };
    vector<vector<struct SubExpr>> Clauses;
    
};

#endif