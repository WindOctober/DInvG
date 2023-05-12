#ifndef INV_DNFEXPR
#define INV_DNFEXPR
#include"clang/AST/ASTContext.h"
#include"clang/AST/ASTConsumer.h"
#include"clang/AST/RecursiveASTVisitor.h"
#include"clang/Analysis/CFG.h"
#include<vector>
#include<string>
using namespace clang;
using namespace std;
enum SExprType{
    
};
struct Term{
    bool primed=false;
    string var;  
};

struct SubExpr{
    enum SExprType type;
    vector<Term> terms;
};

class DExpr{
public:
    DExpr();
    DExpr(Stmt init);
    vector<vector<struct SubExpr>> Clauses;
    DExpr MergeExpr(unique_ptr<DExpr>& expr);

private:

};

#endif