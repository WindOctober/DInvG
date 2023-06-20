#include "Variable.hpp"
#include "Library.hpp"
VariableInfo::VariableInfo()
{
    QualType EmptyType;
    VarName = "";
    VarValue = NULL;
    VarType = EmptyType;
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
        if (Vars[i].getVariableName() == var.getVariableName())
        {
            Vars[i].alterVar("", var.getVariableValue(), Emptytype);
            return;
        }
    }
    Vars.push_back(var);
    return;
}
Expr* VariableInfo::search_for_value(VariableInfo var, vector<VariableInfo> &Vars){
    
    for (int i = 0; i < Vars.size(); i++)
    {
        if (Vars[i].getVariableName() == var.getVariableName())
        {
            if (Vars[i].getVariableValue())
                return Vars[i].getVariableValue();
        }
    }
    return var.getVariableValue();
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

void VariableInfo::alterVar(Expr *var_expr, Expr *init)
{
    if (isa<DeclRefExpr>(var_expr))
    {
        DeclRefExpr *decl = dyn_cast<DeclRefExpr>(var_expr);
        VarName = decl->getDecl()->getNameAsString();
        VarType = decl->getType();
        if (init) VarValue = init;
    }
    else{
        outs()<<"[VariableInfo alterVar warning] Unexpected VarExpr Type that is: "<<var_expr->getStmtClassName()<<'\n';
    }
    return;
}

