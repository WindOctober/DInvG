#include "TransitionSystem.hpp"
#include "Location.h"
#include "var-info.h"
#include "Define.hpp"
#include "TransitionRelation.h"
extern var_info *info, *dual_info, *lambda_info;
extern vector<Location *> *loclist;
extern vector<TransitionRelation *> *trlist;
void TransitionSystem::add_vars(VariableInfo var)
{
    for (int i = 0; i < Canonical_Branch_Count; i++)
    {
        VariableInfo::search_and_insert(var, Vars[i]);
    }
    return;
}

void TransitionSystem::add_expr(Expr *expr)
{
    if (expr == NULL)
        return;
    for (int i = 0; i < Canonical_Branch_Count; i++)
    {
        if (InWhileLoop)
            DNF[i].push_back(expr);
        else
            Init_DNF[i].push_back(expr);
    }
    return;
}

bool TransitionSystem::get_InLoop()
{
    return InWhileLoop;
}
Expr *TransitionSystem::Trans_VariableInfo_to_Expr(VariableInfo var)
{
    // assert(var.getQualType().getAsString()=="int");
    Expr *initExpr = var.getVariableValue();
    VarDecl *VD;
    if (initExpr == NULL)
    {
        return NULL;
    }
    if (var.isInLoop())
        VD = VarDecl::Create(*context, context->getTranslationUnitDecl(), SourceLocation(), SourceLocation(), &context->Idents.get(var.getVariableName()), var.getQualType(), nullptr, SC_None);
    else
        VD = VarDecl::Create(*context, context->getTranslationUnitDecl(), SourceLocation(), SourceLocation(), &context->Idents.get(var.getVariableName() + INITSUFFIX), var.getQualType(), nullptr, SC_None);
    VD->setInit(initExpr);
    DeclRefExpr *LHS = new (context) DeclRefExpr(*context, VD, false, VD->getType(), VK_LValue, SourceLocation(), DeclarationNameLoc(), NOUR_None);
    FPOptions default_options;
    Expr *expr = new (context) BinaryOperator(LHS, var.getVariableValue(), BO_Assign, var.getVariableValue()->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
    return expr;
}

Expr *TransitionSystem::Trans_VariableInfo_to_InitExpr(VariableInfo var)
{
    VarDecl *VD, *VD_init;
    VD = VarDecl::Create(*context, context->getTranslationUnitDecl(), SourceLocation(), SourceLocation(), &context->Idents.get(var.getVariableName()), var.getQualType(), nullptr, SC_None);
    VD_init = VarDecl::Create(*context, context->getTranslationUnitDecl(), SourceLocation(), SourceLocation(), &context->Idents.get(var.getVariableName() + INITSUFFIX), var.getQualType(), nullptr, SC_None);
    DeclRefExpr *LHS = new (context) DeclRefExpr(*context, VD, false, VD->getType(), VK_LValue, SourceLocation(), DeclarationNameLoc(), NOUR_None);
    DeclRefExpr *RHS = new (context) DeclRefExpr(*context, VD_init, false, VD_init->getType(), VK_RValue, SourceLocation(), DeclarationNameLoc(), NOUR_None);
    FPOptions default_options;
    Expr *expr = new (context) BinaryOperator(LHS, RHS, BO_Assign, RHS->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
    return expr;
}

void TransitionSystem::In_Loop()
{
    InWhileLoop = true;
    return;
}

void TransitionSystem::copy_after_update(int size)
{
    for (int i = 0; i < size - 1; i++)
    {
        for (int j = 0; j < Canonical_Branch_Count; j++)
        {
            Vars.push_back(Vars[j]);
            Init_DNF.push_back(Init_DNF[j]);
        }
    }
    Canonical_Branch_Count *= size;
    return;
}

void TransitionSystem::Merge_condition(Expr *condition)
{
    vector<vector<Expr *>> exprs;
    exprs = Deal_with_condition(condition, true, exprs);
    DNF = Merge_DNF(exprs, DNF);
    copy_after_update(exprs.size());
    return;
}
void TransitionSystem::Update_Init_Vars()
{
    if (Init_DNF.size() < Canonical_Branch_Count)
        Init_DNF.resize(Canonical_Branch_Count);
    for (int i = 0; i < Canonical_Branch_Count; i++)
    {
        for (int j = 0; j < Vars[i].size(); j++)
        {
            Expr *assign_expr;
            if (!Vars[i][j].isInLoop())
            {
                assign_expr = Trans_VariableInfo_to_Expr(Vars[i][j]);
                if (assign_expr)
                    Init_DNF[i].push_back(assign_expr);
                assign_expr = Trans_VariableInfo_to_InitExpr(Vars[i][j]);
                if (assign_expr)
                    Init_DNF[i].push_back(assign_expr);
            }
        }
    }
    return;
}

void TransitionSystem::Update_Loop_Vars()
{
    for (int i = 0; i < Canonical_Branch_Count; i++)
    {
        for (int j = 0; j < Vars[i].size(); j++)
        {
            Expr *assign_expr;
            if (Vars[i][j].isInLoop())
            {
                assign_expr = Trans_VariableInfo_to_Expr(Vars[i][j]);
                if (assign_expr)
                    DNF[i].push_back(assign_expr);
            }
            else
                continue;
        }
    }
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
    }
    if (UnaryOperator *unop = dyn_cast<UnaryOperator>(condition))
    {
        if (unop->getOpcode() == UO_LNot)
        {
            return Deal_with_condition(unop->getSubExpr(), !logic, cur);
        }
    }
    assert(cur.size() == 0);
    vector<Expr *> rec_expr;
    if (logic)
    {
        rec_expr.push_back(condition);
    }
    else
    {
        rec_expr.push_back(new (context) UnaryOperator(condition, UO_LNot, condition->getType(), VK_RValue, OK_Ordinary, SourceLocation(), false));
    }
    cur.push_back(rec_expr);
    return cur;
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
            rec_expr.clear();
        }
    }
    return merged_expr;
}

vector<vector<Expr *>> TransitionSystem::Connect_DNF(vector<vector<Expr *>> left_expr, vector<vector<Expr *>> right_expr)
{
    left_expr.insert(left_expr.end(), right_expr.begin(), right_expr.end());
    return left_expr;
}

C_Polyhedron *TransitionSystem::Compute_Init_Poly()
{
}

vector<vector<VariableInfo>> TransitionSystem::get_Used_Vars()
{
    vector<vector<VariableInfo>> res_vars;
    vector<VariableInfo> rec;
    for (int i = 0; i < Canonical_Branch_Count; i++)
    {
    }
}

void TransitionSystem::Compute_Loop_Invariant()
{
    vector<vector<VariableInfo>> vars_in_dnf;
    vars_in_dnf = get_Used_Vars();
    C_Polyhedron *init_poly = Compute_Init_Poly();
}

void TransitionSystem::Out_Loop(WhileStmt *whileloop)
{
    Print_Vars();
    Compute_Loop_Invariant();
    InWhileLoop = false;
    Vars.clear();
    DNF.clear();
    Init_DNF.clear();
    Canonical_Branch_Count = 0;
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

TransitionSystem::TransitionSystem(ASTContext *&astcontext) : context(astcontext)
{
    Vars.clear();
    DNF.clear();
    Init_DNF.clear();
    Verified_Loop_Count = 0;
    Canonical_Branch_Count = 0;
    Inner_Loop_Count = 0;
    Inner_Loop_Depth = 0;
    InWhileLoop = false;
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
    Init_DNF.clear();
    Vars.resize(size);
    DNF.resize(size);
    Init_DNF.resize(size);
    Canonical_Branch_Count = size;
    return;
}

void TransitionSystem::Print_Vars()
{
    outs() << "\n\n";
    outs() << "[Print Variables Information]\n";
    for (int i = 0; i < Vars.size(); i++)
    {
        outs() << "Vars Count " << i << " and its member size is: " << Vars[i].size() << "\n";
        for (int j = 0; j < Vars[i].size(); j++)
        {
            outs() << "\t[Variable Number " << j << " is:]"
                   << "\n";
            outs() << "\t Variable Name is:" << Vars[i][j].getVariableName() << '\n';
            outs() << "\t Variable Value is:";
            if (Vars[i][j].getVariableValue())
            {
                PrintingPolicy Policy(context->getLangOpts());
                string str;
                llvm::raw_string_ostream rso(str);
                (Vars[i][j].getVariableValue())->printPretty(rso, nullptr, Policy);
                rso.flush();
                outs() << str << "\n";
            }
            else
            {
                outs() << "No Initialized." << '\n';
            }

            outs() << "\t Variable InLoop is: " << Vars[i][j].isInLoop() << '\n';
            outs() << "\t Variable Type is: " << Vars[i][j].getQualType().getAsString() << '\n';
        }
    }
}
void TransitionSystem::Print_DNF()
{
    outs() << "\n\n";
    outs() << "[Print DNF Information]\n";
    for (int i = 0; i < DNF.size(); i++)
    {
        outs() << "DNF disjunctive branch " << i << " and its size is:" << DNF[i].size() << '\n';
        for (int j = 0; j < DNF[i].size(); j++)
        {
            outs() << "\t[DNF Number " << j << " is:]"
                   << "\n";
            outs() << "\t";
            PrintingPolicy Policy(context->getLangOpts());
            string str;
            llvm::raw_string_ostream rso(str);
            DNF[i][j]->printPretty(rso, nullptr, Policy);
            rso.flush();
            outs() << str << "\n";
        }
        outs() << "DNF disjunctive clause " << i << " is printed.";
    }
    outs() << "\n";
    outs() << "[Print Init_DNF Information]\n";
    for (int i = 0; i < Init_DNF.size(); i++)
    {
        outs() << "Init_DNF disjunctive branch " << i << " and its size is:" << Init_DNF[i].size() << '\n';
        for (int j = 0; j < Init_DNF[i].size(); j++)
        {
            outs() << "\t[Init_DNF Number " << j << " is:]"
                   << "\n";
            outs() << "\t";
            PrintingPolicy Policy(context->getLangOpts());
            string str;
            llvm::raw_string_ostream rso(str);
            Init_DNF[i][j]->printPretty(rso, nullptr, Policy);
            rso.flush();
            outs() << str << "\n";
        }
        outs() << "Init_DNF disjunctive clause " << i << " is printed.";
    }
    return;
}