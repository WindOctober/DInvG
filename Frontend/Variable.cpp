#include "Variable.hpp"
#include "Define.hpp"

VariableInfo::VariableInfo()
{
    QualType EmptyType;
    VarName = "";
    VarValue = NULL;
    VarType = EmptyType;
    inLoop = false;
    structure_point_flag = false;
    numerical_point_flag = false;
    structure_array_flag = false;
    numerical_array_flag = false;
}
void VariableInfo::search_and_insert(VariableInfo var, vector<VariableInfo> &Vars)
{
    QualType Emptytype;
    for (int i = 0; i < Vars.size(); i++)
    {
        if (Vars[i].getVariableName() == var.getVariableName() && Vars[i].inLoop == var.inLoop)
        {
            Vars[i].alterVar("", var.getVariableValue(), Emptytype, Vars[i].isInLoop());
            return;
        }
    }
    Vars.push_back(var);
    return;
}
Expr* VariableInfo::search_for_value(VariableInfo var, vector<VariableInfo> &Vars){
    
    for (int i = 0; i < Vars.size(); i++)
    {
        if (Vars[i].getVariableName() == var.getVariableName() && Vars[i].inLoop == var.inLoop)
        {
            return Vars[i].getVariableValue();
        }
    }
    return var.getVariableValue();
}

void VariableInfo::alterVar(string varname, Expr *expr, QualType type, bool in)
{
    if (varname != "")
        VarName = varname;
    if (expr != NULL)
        VarValue = expr;
    if (!type.isNull())
        VarType = type;
    inLoop = in;
    return;
}

void VariableInfo::alterVar(Expr *var_expr, Expr *init, bool in)
{
    if (isa<DeclRefExpr>(var_expr))
    {
        DeclRefExpr *decl = dyn_cast<DeclRefExpr>(var_expr);
        VarName = decl->getDecl()->getNameAsString();
        VarType = decl->getType();
        if (init) VarValue = init;
        inLoop = in;
    }
    else{
        outs()<<"[VariableInfo alterVar warning] Unexpected VarExpr Type that is: "<<var_expr->getStmtClassName()<<'\n';
    }
    return;
}