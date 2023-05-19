#ifndef INV_VARIABLE
#define INV_VARIABLE
#include"clang/AST/ASTContext.h"
#include"clang/AST/ASTConsumer.h"
#include"clang/AST/RecursiveASTVisitor.h"
#include"clang/Analysis/CFG.h"
#include <string>

using namespace std;
using namespace clang;
using namespace llvm;

class VariableInfo
{
public:
    string getVariableName();
    const Expr *getVariableValue();
    QualType getQualType();
    void alterVarExpr(Expr *expr);
    VariableInfo() : VarValue(nullptr), VarName("") {}
    void alterVar(string varname,const Expr* expr,QualType type);
private:
    string VarName;
    const Expr *VarValue;
    QualType VarType;
    bool structure_point_flag;
    bool numerical_point_flag;
    bool structure_array_flag;
    bool numerical_array_flag;
    
};

#endif