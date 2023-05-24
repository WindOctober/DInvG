#include "TransitionSystem.hpp"
#include "Location.h"
#include "var-info.h"
#include "Define.hpp"
#include "TransitionRelation.h"
#include "lstingx.h"
#include <unordered_set>
extern var_info *info, *dual_info, *lambda_info;
extern vector<Location *> *loclist;
extern vector<TransitionRelation *> *trlist;

ASTContext *TransitionSystem::context = NULL;
namespace std
{
    template <>
    struct hash<VariableInfo>
    {
        size_t operator()(const VariableInfo &v) const
        {
            size_t string_hash = hash<string>{}(v.getVariableName());
            size_t bool_hash1 = hash<bool>{}(v.getStructurePointer());
            size_t bool_hash2 = hash<bool>{}(v.getNumericalPointer());
            size_t bool_hash3 = hash<bool>{}(v.getNumericalArray());
            size_t bool_hash4 = hash<bool>{}(v.getStructureArray());
            size_t bool_hash5 = hash<bool>{}(v.isInLoop());

            // Combine the hash values. Note that this is a simplistic way to combine hashes,
            // and there are better methods available if collision resistance is important.
            return string_hash ^ bool_hash1 ^ bool_hash2 ^ bool_hash3 ^ bool_hash4 ^ bool_hash5;
        }
    };
}

Expr *TransitionSystem::NegateExpr(Expr *expr)
{
    UnaryOperator *notExpr = new (context) UnaryOperator(expr, UO_LNot, context->BoolTy, VK_RValue, OK_Ordinary, SourceLocation(), false);
    return notExpr;
}

void TransitionSystem::add_vars(VariableInfo& var)
{
    int branch_count = InWhileLoop ? Canonical_Branch_Count : Init_Branch_Count;
    for (int i = 0; i < branch_count; i++)
    {
        if (InWhileLoop)
        {
            VariableInfo::search_and_insert(var, Vars[i]);
        }
        else
            VariableInfo::search_and_insert(var, Init_Vars[i]);
    }
    return;
}

void TransitionSystem::add_vars(VariableInfo& var, Expr *expr)
{
    int branch_count = InWhileLoop ? Canonical_Branch_Count : Init_Branch_Count;
    for (int i = 0; i < branch_count; i++)
    {
        if (InWhileLoop)
        {
            var.alterVar("", Trans_Expr_by_CurVars(expr, Vars[i]), var.getQualType(), InWhileLoop);
            VariableInfo::search_and_insert(var, Vars[i]);
        }
        else{
            var.alterVar("", Trans_Expr_by_CurVars(expr, Init_Vars[i]), var.getQualType(), InWhileLoop);
            VariableInfo::search_and_insert(var, Init_Vars[i]);
        }
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

bool TransitionSystem::check_guard(Expr *expr)
{
    // TODO: make sure the unaryoperator is transformed to be the binop.
    // TODO: make sure the other type in the benchmark won't hurt this funciton.
    if (isa<BinaryOperator>(expr))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
        if (binop->getOpcode() != BO_Assign)
        {
            if (binop->getOpcode() == BO_EQ || binop->getOpcode() == BO_NE || binop->getOpcode() == BO_LT || binop->getOpcode() == BO_GT || binop->getOpcode() == BO_GE || binop->getOpcode() == BO_LE)
            {
                outs() << "\n[check_guard info] The Expr " << Print_Expr(expr) << " is guard";
                return true;
            }
            else
            {
                outs() << "\n[check_guard info] The Expr " << Print_Expr(expr) << " is not guard";
                return false;
            }
        }
        else
        {
            outs() << "\n[check_guard info] The Expr " << Print_Expr(expr) << " is not guard";
            return false;
        }
    }
    else
    {
        outs() << "\n[check_guard warning] The Unexpected Expr type " << Print_Expr(expr) << "";
        return false;
    }
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

void TransitionSystem::Merge_condition(Expr *condition, bool init_flag)
{
    vector<vector<Expr *>> exprs;
    exprs = Deal_with_condition(condition, true, exprs);
    if (!init_flag)
        DNF = Merge_DNF(exprs, DNF);
    else
        Init_DNF = Merge_DNF(exprs, Init_DNF);
    copy_after_update(exprs.size());
    return;
}

TransitionSystem TransitionSystem::Merge_Transystem(TransitionSystem &left_trans, TransitionSystem &right_trans)
{
}

void TransitionSystem::Update_Init_Vars()
{
    for (int i = 0; i < Init_Branch_Count; i++)
    {
        for (int j = 0; j < Init_Vars[i].size(); j++)
        {
            Expr *assign_expr;
            if (!Init_Vars[i][j].isInLoop())
            {
                assign_expr = Trans_VariableInfo_to_Expr(Init_Vars[i][j]);
                if (assign_expr)
                    Init_DNF[i].push_back(assign_expr);
                assign_expr = Trans_VariableInfo_to_InitExpr(Init_Vars[i][j]);
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
        if (isa<BinaryOperator>(condition))
        {
            FPOptions default_options;
            BinaryOperator *binop = dyn_cast<BinaryOperator>(condition);
            Expr *new_binop;
            switch (binop->getOpcode())
            {
            case BO_EQ:
                new_binop = new (context) BinaryOperator(binop->getLHS(), binop->getRHS(), BO_NE, binop->getRHS()->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
                break;
            case BO_LT:
                new_binop = new (context) BinaryOperator(binop->getLHS(), binop->getRHS(), BO_GE, binop->getRHS()->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
                break;
            case BO_LE:
                new_binop = new (context) BinaryOperator(binop->getLHS(), binop->getRHS(), BO_GT, binop->getRHS()->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
                break;
            case BO_GE:
                new_binop = new (context) BinaryOperator(binop->getLHS(), binop->getRHS(), BO_LT, binop->getRHS()->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
                break;
            case BO_GT:
                new_binop = new (context) BinaryOperator(binop->getLHS(), binop->getRHS(), BO_LE, binop->getRHS()->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
                break;
            case BO_NE:
                new_binop = new (context) BinaryOperator(binop->getLHS(), binop->getRHS(), BO_EQ, binop->getRHS()->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
                break;
            default:
                outs() << "\n[Transform unexpected Opcode in BinaryOperator Expr type:]" << binop->getOpcodeStr() << '\n';
            }
            rec_expr.push_back(new_binop);
        }
        else
        {
            outs() << "\n[Deal Contidion Warning] Unexpected type when invert the logic of Expression: " << Print_Expr(condition) << "\n";
            return cur;
        }
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

vector<C_Polyhedron *> TransitionSystem::Compute_and_Eliminate_Init_Poly(vector<VariableInfo> used_vars, Expr *condition)
{
    for (int i = 0; i < Init_Branch_Count; i++)
    {
        for (int j = 0; j < Init_Vars[i].size(); j++)
        {
            string varname = Init_Vars[i][j].getVariableName();
            bool flag = false;
            for (int k = 0; k < used_vars.size(); k++)
            {
                if (used_vars[k].getVariableName() == varname)
                {
                    flag = true;
                    break;
                }
            }
            if (!flag)
            {
                Init_Vars[i].erase(Init_Vars[i].begin() + j);
                j--;
            }
        }
    }
    Update_Init_Vars();
    Merge_condition(condition, true);
    Print_DNF();
    vector<C_Polyhedron *> init_polys;
    for (int i = 0; i < Init_Branch_Count; i++)
    {
        C_Polyhedron *p = new C_Polyhedron(info->get_dimension(), UNIVERSE);
        for (int j = 0; j < Init_DNF[i].size(); j++)
        {
            p->add_constraints(*Trans_Expr_to_Constraints(Init_DNF[i][j], TransformationType::Location, info->get_dimension()));
        }
        init_polys.push_back(p);
    }
    return init_polys;
}

Expr *TransitionSystem::Trans_Expr_by_CurVars(Expr *expr, vector<VariableInfo> &Vars)
{
    if (isa<BinaryOperator>(expr))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
        binop->setLHS(Trans_Expr_by_CurVars(binop->getLHS(), Vars));
        binop->setRHS(Trans_Expr_by_CurVars(binop->getRHS(), Vars));
        return binop;
    }
    else if (isa<DeclRefExpr>(expr))
    {
        DeclRefExpr *declRef = dyn_cast<DeclRefExpr>(expr);
        string name = declRef->getDecl()->getNameAsString();
        VariableInfo var;
        QualType emptyType;
        var.alterVar(name, declRef, emptyType, InWhileLoop);
        return VariableInfo::search_for_value(var, Vars);
    }
    else if (isa<ImplicitCastExpr>(expr))
    {
        ImplicitCastExpr *implict = dyn_cast<ImplicitCastExpr>(expr);
        Trans_Expr_by_CurVars(implict->getSubExpr(), Vars);
    }
    else if (isa<IntegerLiteral>(expr))
    {
    }
    else
    {
        outs() << "[Info] Unexpected Type in Function Trans_Expr_by_CurVars : " << expr->getStmtClassName() << "\n"
               << Print_Expr(expr) << '\n';
        return expr;
    }
    return expr;
}

void TransitionSystem::Traverse_Expr_ForVars(Expr *expr, unordered_set<VariableInfo> &res)
{
    if (isa<BinaryOperator>(expr))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
        Traverse_Expr_ForVars(binop->getLHS(), res);
        Traverse_Expr_ForVars(binop->getRHS(), res);
    }
    else if (isa<DeclRefExpr>(expr))
    {
        DeclRefExpr *declRef = dyn_cast<DeclRefExpr>(expr);
        VariableInfo var;
        Expr *emptyexpr = NULL;
        var.alterVar(declRef, emptyexpr, InWhileLoop);
        res.insert(var);
    }
    else if (isa<ImplicitCastExpr>(expr))
    {
        ImplicitCastExpr *implict = dyn_cast<ImplicitCastExpr>(expr);
        Traverse_Expr_ForVars(implict->getSubExpr(), res);
    }
    else if (isa<IntegerLiteral>(expr))
    {
        return;
    }
    else
    {
        outs() << "[Info] Unexpected Type in Function Traverse_Expr_ForVars : " << expr->getStmtClassName() << "\n"
               << Print_Expr(expr) << '\n';
        exit(0);
    }
    return;
}

void TransitionSystem::Elimiate_Impossible_Path(int size)
{
    for (int i = 0; i < DNF.size(); i++)
    {
        C_Polyhedron *p = new C_Polyhedron(size * 2, UNIVERSE);
        for (int j = 0; j < DNF[i].size(); j++)
        {
            p->add_constraints(*Trans_Expr_to_Constraints(DNF[i][j], TransformationType::Transition, size));
        }

        if (p->is_empty())
        {
            DNF.erase(DNF.begin() + i);
            i--;
        }
    }
    return;
}

void TransitionSystem::Initialize_Locations_and_Transitions(int locsize, int varsize, Expr *condition)
{
    vector<vector<Constraint_System *>> guard;
    guard.resize(DNF.size());
    for (int i = 0; i < DNF.size(); i++)
    {
        for (int j = 0; j < DNF[i].size(); j++)
        {
            if (check_guard(DNF[i][j]))
                guard[i].push_back(Trans_Expr_to_Constraints(DNF[i][j], TransformationType::Guard, varsize));
        }
    }
    for (int i = 0; i < locsize; i++)
    {
        string locname = "Location_" + to_string(i);
        if (i == locsize - 1)
            locname = "le";
        Location *loc = new Location(varsize, info, dual_info, lambda_info, locname);
        loclist->push_back(loc);
    }
    for (int i = 0; i < locsize; i++)
    {
        if (i == locsize - 1)
            continue;
        for (int j = 0; j < locsize; j++)
        {
            string trans_name;
            C_Polyhedron *p;
            p = new C_Polyhedron(varsize * 2, UNIVERSE);
            for (int index = 0; index < DNF[i].size(); index++)
                p->add_constraints(*Trans_Expr_to_Constraints(DNF[i][index], TransformationType::Transition, varsize));
            if (j != locsize - 1)
            {
                for (int index = 0; index < guard[j].size(); index++)
                    p->add_constraints(*guard[j][index]);
                if (p->is_empty())
                    continue;
                trans_name = "Transition_" + to_string(i) + "_" + to_string(j);
                TransitionRelation *trans = new TransitionRelation(varsize, info, dual_info, lambda_info, trans_name);
                trans->set_locs((*loclist)[i], (*loclist)[j]);
                trans->set_relation(p);
                trlist->push_back(trans);
            }
            else
            {
                C_Polyhedron *q = new C_Polyhedron(varsize * 2, UNIVERSE);
                Expr *notExpr = NegateExpr(condition);
                vector<vector<Expr *>> notcond;
                vector<vector<Constraint_System *>> exit_guard;
                notcond = Deal_with_condition(notExpr, true, notcond);
                exit_guard.resize(notcond.size());
                for (int k = 0; k < notcond.size(); k++)
                    for (int index = 0; index < notcond[k].size(); index++)
                        exit_guard[k].push_back(Trans_Expr_to_Constraints(notcond[k][index], TransformationType::Guard, varsize));
                for (int k = 0; k < exit_guard.size(); k++)
                {
                    *q = *p;
                    trans_name = "Exit_Transition_from_" + to_string(i) + "_index_" + to_string(k);
                    for (int index = 0; index < exit_guard[k].size(); index++)
                    {
                        q->add_constraints(*exit_guard[k][index]);
                    }
                    if (q->is_empty())
                        continue;
                    TransitionRelation *trans = new TransitionRelation(varsize, info, dual_info, lambda_info, trans_name);
                    trans->set_locs((*loclist)[i], (*loclist)[j]);
                    trans->set_relation(q);
                    trlist->push_back(trans);
                }
            }
        }
    }
}

vector<VariableInfo> TransitionSystem::get_Used_Vars()
{
    unordered_set<VariableInfo> res_vars_set;
    vector<VariableInfo> res_vars;
    for (int i = 0; i < Canonical_Branch_Count; i++)
    {
        for (int j = 0; j < DNF[i].size(); j++)
        {
            Traverse_Expr_ForVars(DNF[i][j], res_vars_set);
        }
    }
    for (auto it = res_vars_set.begin(); it != res_vars_set.end(); it++)
    {
        res_vars.push_back(*it);
    }
    return res_vars;
}

void TransitionSystem::Compute_Loop_Invariant(Expr *condition)
{
    // DONE: delete the unused variables in init_dnf.
    // DONE: Transform every path into a transition from one path to another.
    // DONE: Construct Location and Transition, and get the invariant , then print.
    // DONE: add variable_init to info.
    // DONE: alter the mode of the Trans_Expr_to_Constraints
    vector<VariableInfo> vars_in_dnf;
    vars_in_dnf = get_Used_Vars();

    info = new var_info();
    lambda_info = new var_info();
    dual_info = new var_info();
    for (int i = 0; i < vars_in_dnf.size(); i++)
    {
        info->search_and_insert(vars_in_dnf[i].getVariableName().c_str());
        info->search_and_insert((vars_in_dnf[i].getVariableName() + INITSUFFIX).c_str());
    }
    vector<C_Polyhedron *> init_polys = Compute_and_Eliminate_Init_Poly(vars_in_dnf, condition);
    Elimiate_Impossible_Path(info->get_dimension());
    int locsize = DNF.size() + 1;
    cout << locsize << endl;
    for (int i = 0; i < init_polys.size(); i++)
    {
        for (int j = 0; j < locsize; j++)
        {
            // TODO: Clarify that what should be clear and how to save the transition information to save time.
            // TODO: Further optimize the implementation of processing poly.
            if (j == locsize - 1)
                continue;
            loclist = new vector<Location *>();
            trlist = new vector<TransitionRelation *>();
            Initialize_Locations_and_Transitions(locsize, info->get_dimension(), condition);
            (*loclist)[j]->set_initial(*init_polys[i]);
            Print_Location_and_Transition();
            Compute_Invariant_Frontend();
        }
    }
}

void TransitionSystem::Out_Loop(WhileStmt *whileloop)
{
    Print_Vars();
    Compute_Loop_Invariant(whileloop->getCond());
    InWhileLoop = false;
    Vars.clear();
    Init_Vars.clear();
    DNF.clear();
    Init_DNF.clear();
    Init_Branch_Count = 0;
    Canonical_Branch_Count = 0;
    Verified_Loop_Count++;
}

void TransitionSystem::Split_If()
{
    if (InWhileLoop)
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
    }
    else
    {
        for (int i = 0; i < Init_Branch_Count; i++)
        {
            Init_Vars.push_back(Init_Vars[i]);
        }
        for (int i = 0; i < Init_Branch_Count; i++)
        {
            Init_DNF.push_back(Init_DNF[i]);
        }
        Init_Branch_Count *= 2;
    }
    return;
}

TransitionSystem::TransitionSystem()
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

TransitionSystem::TransitionSystem(TransitionSystem &other)
    : Verified_Loop_Count(other.Verified_Loop_Count),
      Init_Vars(other.Init_Vars),
      Vars(other.Vars),
      DNF(other.DNF),
      Init_DNF(other.Init_DNF),
      Canonical_Branch_Count(other.Canonical_Branch_Count),
      Init_Branch_Count(other.Init_Branch_Count),
      InWhileLoop(other.InWhileLoop),
      Inner_Loop_Depth(other.Inner_Loop_Depth),
      Inner_Loop_Count(other.Inner_Loop_Count)
{
}

int TransitionSystem::get_Canonical_count()
{
    return Canonical_Branch_Count;
}

Linear_Expression *TransitionSystem::Trans_Expr_to_LinExpr(Expr *expr, enum TransformationType type, int var_size)
{
    Linear_Expression *lin_expr = new Linear_Expression();
    bool flag = (type == TransformationType::Primed);
    if (isa<BinaryOperator>(expr))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
        if (binop->getOpcode() == BO_Add)
        {
            Linear_Expression *left_expr = Trans_Expr_to_LinExpr(binop->getLHS(), type, var_size);
            Linear_Expression *right_expr = Trans_Expr_to_LinExpr(binop->getRHS(), type, var_size);
            *lin_expr = (*left_expr + *right_expr);
        }
        else if (binop->getOpcode() == BO_Sub)
        {
            Linear_Expression *left_expr = Trans_Expr_to_LinExpr(binop->getLHS(), type, var_size);
            Linear_Expression *right_expr = Trans_Expr_to_LinExpr(binop->getRHS(), type, var_size);
            *lin_expr = (*left_expr - *right_expr);
        }
        else if (binop->getOpcode() == BO_Mul)
        {
            Linear_Expression *left_expr = Trans_Expr_to_LinExpr(binop->getLHS(), type, var_size);
            Linear_Expression *right_expr = Trans_Expr_to_LinExpr(binop->getRHS(), type, var_size);
            Coefficient coef;
            if (left_expr->space_dimension() == 0)
            {
                coef = left_expr->inhomogeneous_term();
                *lin_expr = (coef * (*right_expr));
            }
            else if (right_expr->space_dimension() == 0)
            {
                coef = right_expr->inhomogeneous_term();
                *lin_expr = (coef * (*left_expr));
            }
            else
            {
                outs() << "\n[Transform Warning:] Unexpected non-linear expression occur\n"
                       << lin_expr;
                exit(1);
            }
        }
        else
        {
            outs() << "\n[Transform Info:] Unexpected BinaryOperator in Lin_expr:" << binop->getOpcodeStr() << "\n";
        }
    }
    else if (isa<DeclRefExpr>(expr))
    {
        DeclRefExpr *decl = dyn_cast<DeclRefExpr>(expr);
        string var_name = decl->getDecl()->getNameAsString();
        int index = info->search(var_name.c_str());
        if (flag)
            *lin_expr = Variable(index + var_size);
        else
            *lin_expr = Variable(index);
    }
    else if (isa<ParenExpr>(expr))
    {
        ParenExpr *paren = dyn_cast<ParenExpr>(expr);
        lin_expr = Trans_Expr_to_LinExpr(paren->getSubExpr(), type, var_size);
    }
    else if (isa<IntegerLiteral>(expr))
    {
        IntegerLiteral *intexpr = dyn_cast<IntegerLiteral>(expr);
        uint64_t value = intexpr->getValue().getLimitedValue();
        if (value <= numeric_limits<int>::max())
        {
            int intValue = static_cast<int>(value);
            *lin_expr += intValue;
        }
        else
        {
            outs() << "\n[Transform Warning] Unexpected huge value while process interliterals:" << value << "\n";
        }
    }
    else if (isa<UnaryOperator>(expr))
    {
        UnaryOperator *unop = dyn_cast<UnaryOperator>(expr);
        if (unop->getOpcode() == UO_Minus)
        {
            *lin_expr -= *Trans_Expr_to_LinExpr(unop->getSubExpr(), type, var_size);
        }
        else if (unop->getOpcode() == UO_Plus)
        {
            *lin_expr += *Trans_Expr_to_LinExpr(unop->getSubExpr(), type, var_size);
        }
        else
        {
            outs() << "\n[Transform Info:] Unexpected UnaryOperator in Lin_expr:" << unop->getOpcodeStr(unop->getOpcode()) << "\n";
        }
    }
    else if (isa<ImplicitCastExpr>(expr))
    {
        ImplicitCastExpr *implict = dyn_cast<ImplicitCastExpr>(expr);
        lin_expr = Trans_Expr_to_LinExpr(implict->getSubExpr(), type, var_size);
    }
    else
    {
        outs() << "\n[Transform ToLinExpr Warning:] Unexpected Expression Type: " << expr->getStmtClassName() << "\n";
        outs() << "\n[Warning:] Unexpected Expression: " << Print_Expr(expr) << "\n";
    }
    return lin_expr;
}

Constraint_System *TransitionSystem::Trans_Expr_to_Constraints(Expr *expr, enum TransformationType type, int var_size)
{
    // DONE: confirm the expr template, which must be xxx <=/==/>= xxx;
    Constraint_System *constraint = new Constraint_System();
    if (check_guard(expr))
    {
        if (type == TransformationType::Transition)
        {
            type = TransformationType::Origin;
        }
        else if (type == TransformationType::Guard)
        {
            type = TransformationType::Primed;
        }
        else if (type == TransformationType::Location)
        {
            type = TransformationType::Origin;
        }
        if (isa<BinaryOperator>(expr))
        {
            BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
            if (binop->getOpcode() == BO_EQ)
            {
                Linear_Expression *left_expr = Trans_Expr_to_LinExpr(binop->getLHS(), type, var_size);
                Linear_Expression *right_expr = Trans_Expr_to_LinExpr(binop->getRHS(), type, var_size);
                constraint->insert((*left_expr) == (*right_expr));
            }
            else if (binop->getOpcode() == BO_LT)
            {
                Linear_Expression *left_expr = Trans_Expr_to_LinExpr(binop->getLHS(), type, var_size);
                Linear_Expression *right_expr = Trans_Expr_to_LinExpr(binop->getRHS(), type, var_size);
                constraint->insert((*left_expr) <= (*right_expr - 1));
            }
            else if (binop->getOpcode() == BO_LE)
            {
                Linear_Expression *left_expr = Trans_Expr_to_LinExpr(binop->getLHS(), type, var_size);
                Linear_Expression *right_expr = Trans_Expr_to_LinExpr(binop->getRHS(), type, var_size);
                constraint->insert((*left_expr) <= (*right_expr));
            }
            else if (binop->getOpcode() == BO_GE)
            {
                Linear_Expression *left_expr = Trans_Expr_to_LinExpr(binop->getLHS(), type, var_size);
                Linear_Expression *right_expr = Trans_Expr_to_LinExpr(binop->getRHS(), type, var_size);
                constraint->insert((*left_expr) >= (*right_expr));
            }
            else if (binop->getOpcode() == BO_GT)
            {
                Linear_Expression *left_expr = Trans_Expr_to_LinExpr(binop->getLHS(), type, var_size);
                Linear_Expression *right_expr = Trans_Expr_to_LinExpr(binop->getRHS(), type, var_size);
                constraint->insert((*left_expr - 1) >= (*right_expr));
            }
            else if (binop->getOpcode() == BO_NE)
            {
                Linear_Expression *left_expr = Trans_Expr_to_LinExpr(binop->getLHS(), type, var_size);
                Linear_Expression *right_expr = Trans_Expr_to_LinExpr(binop->getRHS(), type, var_size);
                constraint->insert((*left_expr) <= (*right_expr - 1));
                constraint->insert((*left_expr) >= (*right_expr + 1));
            }
            else
            {
                outs() << "\n[Transform unexpected Opcode in BinaryOperator Expr type:]" << binop->getOpcodeStr() << '\n';
                exit(1);
            }
        }
    }
    else
    {
        if (type == TransformationType::Guard)
        {
            outs() << "\n[Transform unexpected Opcode in Guard Expr type: " << Print_Expr(expr) << "]\n";
        }
        if (isa<BinaryOperator>(expr))
        {
            BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
            if (binop->getOpcode() == BO_Assign)
            {
                VariableInfo var;
                var.alterVar(binop->getLHS(), binop->getRHS(), InWhileLoop);
                int index = info->search(var.getVariableName().c_str());
                if (type == TransformationType::Transition)
                    index += var_size;
                type = TransformationType::Origin;
                Linear_Expression *left_expr = new Linear_Expression(Variable(index));
                Linear_Expression *right_expr = Trans_Expr_to_LinExpr(binop->getRHS(), type, var_size);
                constraint->insert((*left_expr) == (*right_expr));
            }
        }
        else
        {
            outs() << "\n[Transform unexpected Expr type: " << expr->getStmtClassName() << "]\n";
            exit(1);
        }
    }
    return constraint;
}

void TransitionSystem::init_Canonical(int size)
{
    Vars.clear();
    DNF.clear();
    Init_Vars.clear();
    Init_DNF.clear();
    Vars.resize(size);
    DNF.resize(size);
    Init_DNF.resize(size);
    Init_Vars.resize(size);
    Init_Branch_Count = size;
    Canonical_Branch_Count = size;
    return;
}

void TransitionSystem::Print_Vars()
{
    outs() << "\n\n";
    outs() << "[Print Init Variables Information]\n";
    for (int i = 0; i < Init_Vars.size(); i++)
    {
        outs() << "Vars Count " << i << " and its member size is: " << Init_Vars[i].size() << "\n";
        for (int j = 0; j < Init_Vars[i].size(); j++)
        {
            outs() << "\t[Variable Number " << j << " is:]"
                   << "\n";
            outs() << "\t Variable Name is:" << Init_Vars[i][j].getVariableName() << '\n';
            outs() << "\t Variable Value is:";
            if (Init_Vars[i][j].getVariableValue())
            {
                outs() << Print_Expr(Init_Vars[i][j].getVariableValue()) << "\n";
            }
            else
            {
                outs() << "No Initialized." << '\n';
            }

            outs() << "\t Variable InLoop is: " << Init_Vars[i][j].isInLoop() << '\n';
            outs() << "\t Variable Type is: " << Init_Vars[i][j].getQualType().getAsString() << '\n';
        }
    }
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
                outs() << Print_Expr(Vars[i][j].getVariableValue()) << "\n";
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

            outs() << Print_Expr(Init_DNF[i][j]) << "\n";
        }
        outs() << "Init_DNF disjunctive clause " << i << " is printed.";
    }
    return;
}