#include "TransitionSystem.hpp"
#include "Location.h"
#include "var-info.h"
#include "Library.hpp"
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

            // Combine the hash values. Note that this is a simplistic way to combine hashes,
            // and there are better methods available if collision resistance is important.
            return string_hash ^ bool_hash1 ^ bool_hash2 ^ bool_hash3 ^ bool_hash4;
        }
    };
}

Expr *TransitionSystem::NegateExpr(Expr *expr)
{
    UnaryOperator *notExpr = new (context) UnaryOperator(expr, UO_LNot, context->BoolTy, VK_RValue, OK_Ordinary, SourceLocation(), false);
    return notExpr;
}

void TransitionSystem::add_comment(ACSLComment *comment)
{
    comments.push_back(comment);
    return;
}

void TransitionSystem::add_vars(VariableInfo &var)
{
    if (Vars.size() == 0)
    {
        Vars.resize(1);
    }
    for (int i = 0; i < Vars.size(); i++)
    {
        VariableInfo::search_and_insert(var, Vars[i]);
    }
    return;
}

void TransitionSystem::add_vars(VariableInfo &var, Expr *expr)
{
    if (Vars.size() == 0)
    {
        Vars.resize(1);
    }
    for (int i = 0; i < Vars.size(); i++)
    {
        var.alterVar("", Trans_Expr_by_CurVars(expr, Vars[i]), var.getQualType());
        VariableInfo::search_and_insert(var, Vars[i]);
    }
    return;
}

void TransitionSystem::add_expr(Expr *expr)
{
    if (expr == NULL)
        return;
    if (DNF.size() == 0)
    {
        DNF.resize(1);
    }
    for (int i = 0; i < DNF.size(); i++)
    {
        DNF[i].push_back(expr);
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
    VD = VarDecl::Create(*context, context->getTranslationUnitDecl(), SourceLocation(), SourceLocation(), &context->Idents.get(var.getVariableName()), var.getQualType(), nullptr, SC_None);
    VD->setInit(initExpr);
    DeclRefExpr *LHS = new (context) DeclRefExpr(*context, VD, false, VD->getType(), VK_LValue, SourceLocation(), DeclarationNameLoc(), NOUR_None);
    FPOptions default_options;
    Expr *expr = new (context) BinaryOperator(LHS, var.getVariableValue(), BO_Assign, var.getVariableValue()->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
    return expr;
}

void TransitionSystem::In_Loop()
{
    InWhileLoop = true;
    DNF.clear();
    Vars.clear();
    return;
}

unordered_set<string> TransitionSystem::get_Used_Vars()
{
    unordered_set<string> used_vars;
    for (int i = 0; i < DNF.size(); i++)
    {
        for (int j = 0; j < DNF[i].size(); j++)
        {
            Traverse_Expr_ForVars(DNF[i][j], used_vars);
        }
    }
    return used_vars;
}

void TransitionSystem::copy_after_update(int size)
{
    for (int i = 0; i < size - 1; i++)
    {
        for (int j = 0; j < DNF.size(); j++)
        {
            Vars.push_back(Vars[j]);
            DNF.push_back(DNF[j]);
        }
    }
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

TransitionSystem TransitionSystem::Merge_Transystem(TransitionSystem &left_trans, TransitionSystem &right_trans)
{
    return right_trans;
}

void TransitionSystem::Update_Vars()
{
    for (int i = 0; i < Vars.size(); i++)
    {
        for (int j = 0; j < Vars[i].size(); j++)
        {
            Expr *assign_expr;
            assign_expr = Trans_VariableInfo_to_Expr(Vars[i][j]);
            if (assign_expr)
                DNF[i].push_back(assign_expr);
        }
    }
    return;
}

vector<vector<Expr *>> TransitionSystem::Deal_with_condition(Expr *condition, bool logic)
{
    vector<vector<Expr *>> cur;
    return Deal_with_condition(condition, logic, cur);
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
        var.alterVar(name, declRef, emptyType);
        Print_Vars();
        return VariableInfo::search_for_value(var, Vars);
    }
    else if (isa<ImplicitCastExpr>(expr))
    {
        ImplicitCastExpr *implict = dyn_cast<ImplicitCastExpr>(expr);
        return Trans_Expr_by_CurVars(implict->getSubExpr(), Vars);
    }
    else if (isa<IntegerLiteral>(expr))
    {
    }
    else
    {
        outs() << "[Info] Unexpected Type in Function Trans_Expr_by_CurVars : " << expr->getStmtClassName() << "\n"
               << Print_Expr(expr) << '\n';
    }
    return expr;
}

void TransitionSystem::Elimiate_Impossible_Path(int size)
{
    for (int i = 0; i < DNF.size(); i++)
    {
        C_Polyhedron *p = new C_Polyhedron(size * 2, UNIVERSE);
        for (int j = 0; j < DNF[i].size(); j++)
        {
            p->add_constraints(*Trans_Expr_to_Constraints(DNF[i][j], TransformationType::Trans, size));
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
                p->add_constraints(*Trans_Expr_to_Constraints(DNF[i][index], TransformationType::Trans, varsize));
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

void TransitionSystem::Compute_Loop_Invariant(Expr *condition, unordered_set<string> vars_in_dnf, vector<C_Polyhedron> init_polys)
{
    // DONE: delete the unused variables in init_dnf.
    // DONE: Transform every path into a transition from one path to another.
    // DONE: Construct Location and Transition, and get the inequality_DNF , then print.
    // DONE: add variable_init to info.
    // DONE: alter the mode of the Trans_Expr_to_Constraints
    if (comments.size() == 0)
    {
        LOG_WARNING("No Comments has been added to the transystem.");
        exit(0);
    }
    ACSLComment *loop_comment = get_CurComment();
    info = new var_info();
    lambda_info = new var_info();
    dual_info = new var_info();

    for (const auto &var : vars_in_dnf)
    {
        info->search_and_insert(var.c_str());
        info->search_and_insert((var + INITSUFFIX).c_str());
    }
    Elimiate_Impossible_Path(info->get_dimension());
    int locsize = DNF.size() + 1;
    cout << locsize << endl;
    inequality_DNF.clear();
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
            (*loclist)[j]->set_initial(init_polys[i]);
            Print_Location_and_Transition();
            Compute_Invariant_Frontend();
            vector<C_Polyhedron> loc_invariant = (*loclist)[locsize - 1]->get_vp_inv().get_vp();
            inequality_DNF = Merge_DNF(inequality_DNF, Trans_Polys_to_Exprs(loc_invariant));
            loop_comment->add_invariant(loc_invariant);
            loc_invariant.clear();
            for (int index = 0; index < locsize - 1; index++)
            {
                loc_invariant.push_back((*loclist)[index]->get_invariant());
            }
            loop_comment->add_invariant(Trans_Polys_to_Exprs(loc_invariant));
        }
    }
    loop_comment->add_assign_vars(vars_in_dnf);
    Print_DNF();
    if (loclist != NULL && trlist != NULL)
        delete loclist, trlist;
    delete info, dual_info, lambda_info;
    return;
}

void TransitionSystem::Out_Loop(WhileStmt *whileloop, unordered_set<string>& used_vars, vector<vector<Expr *>>& init_DNF)
{
    Print_Vars();
    vector<C_Polyhedron> init_polys=Compute_and_Eliminate_Init_Poly(used_vars,whileloop->getCond(),init_DNF,inequality_DNF);
    Compute_Loop_Invariant(whileloop->getCond(), used_vars, init_polys);
    ACSLComment* comment = get_CurComment();
    // TODO: add the remaining DNF into the comment.
    InWhileLoop = false;
    Vars.clear();
    DNF.clear();
    Verified_Loop_Count++;
}

void TransitionSystem::Split_If()
{
    for (int i = 0; i < Vars.size(); i++)
    {
        Vars.push_back(Vars[i]);
    }
    for (int i = 0; i < DNF.size(); i++)
    {
        DNF.push_back(DNF[i]);
    }
    return;
}

TransitionSystem::TransitionSystem()
{
    Vars.clear();
    DNF.clear();
    Verified_Loop_Count = 0;
    Inner_Loop_Count = 0;
    Inner_Loop_Depth = 0;
    InWhileLoop = false;
}

TransitionSystem::TransitionSystem(TransitionSystem &other)
    : Verified_Loop_Count(other.Verified_Loop_Count),
      Vars(other.Vars),
      DNF(other.DNF),
      InWhileLoop(other.InWhileLoop),
      Inner_Loop_Depth(other.Inner_Loop_Depth),
      Inner_Loop_Count(other.Inner_Loop_Count)
{
}

void TransitionSystem::init_Canonical(int size)
{
    Vars.clear();
    DNF.clear();
    Vars.resize(size);
    DNF.resize(size);
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
                outs() << Print_Expr(Vars[i][j].getVariableValue()) << "\n";
            }
            else
            {
                outs() << "No Initialized." << '\n';
            }
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
    outs() << "[Print inequality_DNF Information]\n";
    for (int i = 0; i < inequality_DNF.size(); i++)
    {
        outs() << "inequality_DNF disjunctive branch " << i << " and its size is:" << inequality_DNF[i].size() << '\n';
        for (int j = 0; j < inequality_DNF[i].size(); j++)
        {
            outs() << "\t[inequality_DNF Number " << j << " is:]"
                   << "\n";
            outs() << "\t";

            outs() << Print_Expr(inequality_DNF[i][j]) << "\n";
        }
        outs() << "inequality_DNF disjunctive clause " << i << " is printed.";
    }
    return;
}
