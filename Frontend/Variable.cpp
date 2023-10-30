#include "Variable.hpp"
#include "Library.hpp"
#include "TransitionSystem.hpp"

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
void VariableInfo::searchElseInsert(VariableInfo var, vector<VariableInfo> &Vars)
{
    QualType Emptytype;
    for (int i = 0; i < Vars.size(); i++)
    {
        if (Vars[i].getVarName() == var.getVarName())
        {
            Vars[i].assign("", var.getVarValue(), Emptytype);
            return;
        }
    }
    Vars.push_back(var);
    return;
}
Expr *VariableInfo::search_for_value(VariableInfo var, vector<VariableInfo> &Vars)
{

    for (int i = 0; i < Vars.size(); i++)
    {
        if (Vars[i].getVarName() == var.getVarName())
        {
            if (Vars[i].getVarValue())
                return Vars[i].getVarValue();
        }
    }
    return var.getVarValue();
}

void VariableInfo::assign(string varname, Expr *expr, QualType type)
{
    if (varname != "")
        VarName = varname;
    if (expr != NULL)
        VarValue = expr;
    if (!type.isNull())
        VarType = type;
    return;
}

void VariableInfo::assign(Expr *var_expr, Expr *init)
{
    if (isa<DeclRefExpr>(var_expr))
    {
        DeclRefExpr *decl = dyn_cast<DeclRefExpr>(var_expr);
        VarName = decl->getDecl()->getNameAsString();
        VarType = decl->getType();
        if (init)
            VarValue = init;
    }
    else if (isa<UnaryOperator>(var_expr))
    {
        UnaryOperator *unop = dyn_cast<UnaryOperator>(var_expr);
        if (unop->getOpcode() == UO_Deref)
        {
            Expr *subexpr = unop->getSubExpr();
            DeclRefExpr *decl;
            if (isa<ImplicitCastExpr>(subexpr))
            {
                ImplicitCastExpr *implicit = dyn_cast<ImplicitCastExpr>(subexpr);
                subexpr = implicit->getSubExpr();
            }
            if (isa<DeclRefExpr>(subexpr))
            {
                decl = dyn_cast<DeclRefExpr>(subexpr);
                decl = createDeclRefExpr("*" + decl->getDecl()->getNameAsString());
                assign(decl, init);
            }
            else if (isa<UnaryOperator>(subexpr))
            {
                UnaryOperator *unop = dyn_cast<UnaryOperator>(subexpr);
                ArrIndex RecArrIndex;
                if (unop->getOpcode() == UO_PostInc)
                    RecArrIndex.InitIndex = 0;
                else if (unop->getOpcode() == UO_PreInc)
                    RecArrIndex.InitIndex = 1;
                if (unop->getOpcode() == UO_PostDec || unop->getOpcode() == UO_PreDec)
                {
                    LOGWARN("unexpected Array Mode");
                    exit(-1);
                }
                RecArrIndex.IndexName = MakeIndexName();
                ArrayIndex.push_back(RecArrIndex);
            }
            else
            {
                LOGWARN("Unexpected Expr type:" + string(subexpr->getStmtClassName()));
                exit(-1);
            }
            return;
        }
    }
    else if (isa<ImplicitCastExpr>(var_expr))
    {
        ImplicitCastExpr *implicit = dyn_cast<ImplicitCastExpr>(var_expr);
        assign(implicit->getSubExpr(), init);
        return;
    }
    else if (isa<ArraySubscriptExpr>(var_expr))
    {
        ArraySubscriptExpr *array = dyn_cast<ArraySubscriptExpr>(var_expr);
        VarType = var_expr->getType();
        VarName = PrintExpr(var_expr);
        if (init)
            VarValue = init;
        Expr *IndexExpr;
        Expr *BaseExpr;
        do
        {
            IndexExpr = array->getIdx();
            BaseExpr = array->getBase();
            if (isa<ImplicitCastExpr>(BaseExpr))
                BaseExpr = (dyn_cast<ImplicitCastExpr>(BaseExpr))->getSubExpr();
            if (isa<ImplicitCastExpr>(IndexExpr))
                IndexExpr = (dyn_cast<ImplicitCastExpr>(IndexExpr))->getSubExpr();
            if (isa<DeclRefExpr>(IndexExpr))
            {
                ArrIndex RecArrIndex;
                RecArrIndex.IndexName = (dyn_cast<DeclRefExpr>(IndexExpr))->getDecl()->getNameAsString();
                bool flag = true;
                for (int i = 0; i < ArrayIndex.size(); i++)
                {
                    if (RecArrIndex.IndexName == ArrayIndex[i].IndexName)
                    {
                        flag = false;
                        break;
                    }
                }
                if (flag)
                    ArrayIndex.push_back(RecArrIndex);
            }
            else if (IndexExpr->isConstantInitializer(*TransitionSystem::context, false))
            {
            }
            else
            {
                LOGWARN("Unexpected Mode of Array:" + PrintExpr(IndexExpr));
                LOGWARN("Type: " + string(IndexExpr->getStmtClassName()));
                exit(-1);
            }
        } while (!isa<DeclRefExpr>(BaseExpr));
    }
    else if (isa<ParenExpr>(var_expr))
    {
        ParenExpr *paren = dyn_cast<ParenExpr>(var_expr);
        assign(paren->getSubExpr(), init);
    }
    else
    {
        LOGWARN("Unexpected VarExpr Type that is: ");
        LOGWARN(var_expr->getStmtClassName());
        exit(-1);
    }
    return;
}
