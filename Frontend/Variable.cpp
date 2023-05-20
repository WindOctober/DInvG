#include "Variable.hpp"

string VariableInfo::getVariableName()
{
    return VarName;
}

Expr *VariableInfo::getVariableValue()
{
    return VarValue;
}

QualType VariableInfo::getQualType()
{
    return VarType;
}

bool VariableInfo::isPreVar(){
    return pre_var;
}

void VariableInfo::alterVarExpr(Expr *expr)
{
    VarValue = expr;
}

void VariableInfo::search_and_insert(VariableInfo var, vector<VariableInfo>& Vars)
{
    QualType Emptytype;
    for(int i=0;i<Vars.size();i++) {
        if (Vars[i].getVariableName()==var.getVariableName() ){
            Vars[i].alterVar("",var.getVariableValue(),Emptytype);
            return;
        }
    }
    Vars.push_back(var);
    return;
}

void VariableInfo::alterVar(string varname, Expr *expr, QualType type)
{
    if (varname != "")
        VarName = varname;
    if (expr != NULL)
        VarValue = expr;
    if (!type.isNull())
        VarType = type;
    return;
}