#include "CFGVisitor.hpp"
#include<string>
class VariableInfo
{
public:
    string getVariableName();
    const Expr *getVariableValue();
    QualType getQualType();
    void alterVarExpr(Expr *expr);
    VariableInfo() : VarValue(nullptr), VarName("") {}

private:
    string VarName;
    const Expr *VarValue;
    QualType VarType;
};