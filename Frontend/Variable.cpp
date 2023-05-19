#include "Variable.hpp"

string VariableInfo::getVariableName()
{
    return VarName;
}

const Expr *VariableInfo::getVariableValue()
{
    return VarValue;
}

QualType VariableInfo::getQualType()
{
    return VarType;
}

void VariableInfo::alterVarExpr(Expr *expr)
{
    VarValue = expr;
}