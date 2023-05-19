#include "TransitionSystem.hpp"

void TransitionSystem::add_vars(VariableInfo var, int left, int right)
{
    for (int i = left; i <= right; i++)
    {
        Vars[i].push_back(var);
    }
    return;
}

void TransitionSystem::In_Loop(Expr *condition)
{
    InWhileLoop = true;
    vector<vector<Expr *>> exprs;
    exprs=Deal_with_condition(condition, true, exprs);
    DNF=Merge_DNF(DNF,exprs);
    return;
}

vector<vector<Expr *>> TransitionSystem::Deal_with_condition(Expr *condition, bool logic, vector<vector<Expr *>> cur)
{
    vector<vector<Expr *>> left_expr;
    vector<vector<Expr *>> right_expr;
    if (BinaryOperator *binop = dyn_cast<BinaryOperator>(condition))
    {
        if (binop->getOpcode() == BO_LAnd)
        {
            if (logic)
            {
                left_expr = Deal_with_condition(binop->getLHS(), logic, cur);
                right_expr = Deal_with_condition(binop->getRHS(), logic, cur);
                return Merge_DNF(left_expr, right_expr);
            }
            else
            {
                left_expr = Deal_with_condition(binop->getLHS(), logic, cur);
                right_expr = Deal_with_condition(binop->getRHS(), logic, cur);
                return Connect_DNF(left_expr, right_expr);
            }
        }
        else if (binop->getOpcode() == BO_LOr)
        {
            if (!logic)
            {
                left_expr = Deal_with_condition(binop->getLHS(), logic,cur);
                right_expr = Deal_with_condition(binop->getRHS(), logic,cur);
                return Merge_DNF(left_expr, right_expr);
            }
            else{
                left_expr = Deal_with_condition(binop->getLHS(), logic,cur);
                right_expr = Deal_with_condition(binop->getRHS(), logic,cur);
                return Connect_DNF(left_expr, right_expr);
            }
        }
    }
    if (UnaryOperator *unop = dyn_cast<UnaryOperator>(condition))
    {
        if (unop->getOpcode() == UO_LNot)
        {
            return Deal_with_condition(unop->getSubExpr(), !logic,cur);
        }
    }
    assert(cur.size()==0);
    vector<Expr*> rec_expr;
    if (logic)
    {
        rec_expr.push_back(condition);
    }
    else{
        rec_expr.push_back(new (context) UnaryOperator(condition,UO_LNot, condition->getType(), VK_RValue, OK_Ordinary, SourceLocation(),false));
    }
}

vector<vector<Expr *>> TransitionSystem::Merge_DNF(vector<vector<Expr *>> left_expr, vector<vector<Expr *>> right_expr)
{
    vector<vector<Expr *>> merged_expr;
    vector<Expr *> rec_expr;
    for (int i = 0; i < left_expr.size(); i++)
    {
        for (int j = 0; j < right_expr.size(); j++)
        {
            rec_expr.insert(rec_expr.end(), left_expr[i].begin(), left_expr[i].end());
            rec_expr.insert(rec_expr.end(), right_expr[j].begin(), right_expr[j].end());
            merged_expr.push_back(rec_expr);
        }
    }
    return merged_expr;
}

vector<vector<Expr *>> TransitionSystem::Connect_DNF(vector<vector<Expr *>> left_expr, vector<vector<Expr *>> right_expr)
{
    left_expr.insert(left_expr.end(), right_expr.begin(), right_expr.end());
    return left_expr;
}

void TransitionSystem::Out_Loop()
{
    InWhileLoop = false;
    Vars.clear();
    DNF.clear();
    Verified_Loop_Count++;
}

void TransitionSystem::Split_If()
{
    for (int i = 0; i < Canonical_Branch_Count; i++)
    {
        Vars.push_back(Vars[i]);
    }
    for (int i = 0; i < Canonical_Branch_Count; i++)
    {
        DNF.push_back(DNF[i]);
    }
    Canonical_Branch_Count *= 2;
    return;
}

TransitionSystem::TransitionSystem(ASTContext *context)
{
    Vars.clear();
    DNF.clear();
    Verified_Loop_Count = 0;
    Canonical_Branch_Count = 0;
    InWhileLoop = false;
    context = context;
}

int TransitionSystem::get_Canonical_count()
{
    return Canonical_Branch_Count;
}

Constraint *TransitionSystem::Trans_Expr_to_Constraint(Expr *expr)
{
}

void TransitionSystem::init_Canonical(int size)
{
    Vars.clear();
    DNF.clear();
    Vars.resize(size);
    DNF.resize(size);
    Canonical_Branch_Count = size;
    return;
}

void TransitionSystem::add_condition_all(Expr *expr)
{
    for (int i = 0; i < DNF.size(); i++)
    {
        DNF[i].push_back(expr);
    }
    return;
}