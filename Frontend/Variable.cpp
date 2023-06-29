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
    else if (isa<UnaryOperator>(var_expr)){
        UnaryOperator *unop=dyn_cast<UnaryOperator>(var_expr);
        if (unop->getOpcode()==UO_Deref){
            alterVar(unop->getSubExpr(),init);
            return;
        }
    }
    else if (isa<ImplicitCastExpr>(var_expr)){
        ImplicitCastExpr *implicit=dyn_cast<ImplicitCastExpr>(var_expr);
        alterVar(implicit->getSubExpr(),init);
        return;
    }
    else{
        LOG_WARNING("Unexpected VarExpr Type that is: ");
        LOG_WARNING(var_expr->getStmtClassName());
        exit(0);
    }
    return;
}

