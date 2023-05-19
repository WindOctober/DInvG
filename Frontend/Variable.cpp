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

void VariableInfo::alterVar(string varname,const Expr* expr,QualType type){
    if (varname != "")
        VarName=varname;
    if (expr != NULL)
        VarValue=expr;
    if (!type.isNull())
        VarType=type;
    return;
}