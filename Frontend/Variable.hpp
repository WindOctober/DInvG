#ifndef INV_VARIABLE
#define INV_VARIABLE
#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Analysis/CFG.h"
#include <string>

using namespace std;
using namespace clang;
using namespace llvm;

class VariableInfo
{
public:
    VariableInfo();
    string getVariableName();
    Expr *getVariableValue();
    QualType getQualType();

    static void search_and_insert(VariableInfo var, vector<VariableInfo> &Vars);
    void alterVar(string varname, Expr *expr, QualType type, bool inloop);
    void alterVar(Expr *var_expr, Expr *init, bool in);

    bool isInLoop();

private:
    string VarName;
    Expr *VarValue;
    QualType VarType;
    bool structure_point_flag;
    bool numerical_point_flag;
    bool structure_array_flag;
    bool numerical_array_flag;

    bool inLoop;
};

#endif