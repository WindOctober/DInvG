#include "TransitionSystem.hpp"
#include "Location.h"
#include "var-info.h"
#include "Library.hpp"
#include "TransitionRelation.h"
#include "lstingx.h"
#include <regex>
#include <unordered_set>
extern var_info *info, *dualInfo, *lambdaInfo;
extern vector<Location *> *loclist;
extern vector<TransitionRelation *> *trlist;
extern unordered_set<string> global_vars;
extern set<string> MainFuncs;
vector<ArrIndex> ArrayIndex;
ASTContext *TransitionSystem::context = NULL;
namespace std
{
    template <>
    struct hash<VariableInfo>
    {
        size_t operator()(const VariableInfo &v) const
        {
            size_t string_hash = hash<string>{}(v.getVarName());
            size_t bool_hash1 = hash<bool>{}(v.getStructurePointer());
            size_t bool_hash2 = hash<bool>{}(v.getNumericalPointer());
            size_t bool_hash3 = hash<bool>{}(v.getNumericalArray());
            size_t bool_hash4 = hash<bool>{}(v.getStructureArray());

            return string_hash ^ bool_hash1 ^ bool_hash2 ^ bool_hash3 ^ bool_hash4;
        }
    };
}

DeclRefExpr *createDeclRefExpr(string name)
{
    ASTContext *context = TransitionSystem::context;
    VarDecl *VD = VarDecl::Create(*context, context->getTranslationUnitDecl(), SourceLocation(), SourceLocation(), &context->Idents.get(name), context->IntTy, nullptr, SC_None);
    DeclRefExpr *RefExpr = new (context) DeclRefExpr(*context, VD, false, VD->getType(), VK_LValue, SourceLocation(), DeclarationNameLoc(), NOUR_None);
    return RefExpr;
}

BinaryOperator *createBinOp(Expr *left, Expr *right, BinaryOperatorKind kind)
{
    ASTContext *context = TransitionSystem::context;
    QualType resultType = left->getType();
    FPOptions default_option;
    BinaryOperator *Binop = new (context) BinaryOperator(left, right, kind, resultType, VK_RValue, OK_Ordinary, SourceLocation(), default_option);
    return Binop;
}

UnaryOperator *createUnOp(Expr *expr, UnaryOperatorKind kind)
{
    ASTContext *context = TransitionSystem::context;
    QualType resultType = expr->getType();
    UnaryOperator *Unop = new (context) UnaryOperator(expr, kind, resultType, VK_RValue, OK_Ordinary, SourceLocation(), false);
    return Unop;
}

IntegerLiteral *createIntegerLiteral(int val)
{
    ASTContext *context = TransitionSystem::context;
    IntegerLiteral *value = IntegerLiteral::Create(*context, APInt(context->getIntWidth(context->IntTy), val), context->IntTy, SourceLocation());
    return value;
}

bool CheckBreakFlag(Expr *expr)
{
    if (isa<DeclRefExpr>(expr))
    {
        DeclRefExpr *decl = dyn_cast<DeclRefExpr>(expr);
        if (decl->getDecl()->getNameAsString() == "break")
            return true;
        else
            return false;
    }
    else
        return false;
}
void TransitionSystem::PrintDNF(vector<vector<Expr *>> DNF)
{
    outs() << "\n\n";
    outs() << "[Print SelfDefined DNF Information]\n";
    for (int i = 0; i < DNF.size(); i++)
    {
        outs() << "DNF disjunctive branch " << i << " and its size is:" << DNF[i].size() << '\n';
        for (int j = 0; j < DNF[i].size(); j++)
        {
            outs() << "\t[DNF Number " << j << " is:]"
                   << "\n";
            outs() << "\t";
            PrintingPolicy Policy(TransitionSystem::context->getLangOpts());
            string str;
            raw_string_ostream rso(str);
            DNF[i][j]->printPretty(rso, nullptr, Policy);
            rso.flush();
            outs() << str << "\n";
        }
        outs() << "DNF disjunctive clause " << i << " is printed.\n";
    }
    return;
}

void PrintDNF(vector<vector<Expr *>> &DNF)
{
    outs() << "\n\n";
    outs() << "[Print SelfDefined DNF Information]\n";
    for (int i = 0; i < DNF.size(); i++)
    {
        outs() << "DNF disjunctive branch " << i << " and its size is:" << DNF[i].size() << '\n';
        for (int j = 0; j < DNF[i].size(); j++)
        {
            outs() << "\t[DNF Number " << j << " is:]"
                   << "\n";
            outs() << "\t";
            PrintingPolicy Policy(TransitionSystem::context->getLangOpts());
            string str;
            raw_string_ostream rso(str);
            DNF[i][j]->printPretty(rso, nullptr, Policy);
            rso.flush();
            outs() << str << "\n";
        }
        outs() << "DNF disjunctive clause " << i << " is printed.\n";
    }
    return;
}

string PrintExpr(Expr *expr)
{
    PrintingPolicy Policy(TransitionSystem::context->getLangOpts());
    string str;
    raw_string_ostream rso(str);
    expr->printPretty(rso, nullptr, Policy);
    rso.flush();
    return str;
}

bool check_guard(Expr *expr)
{
    // TODO: make sure the unaryoperator is transformed to be the binop.
    // TODO: make sure the other type in the benchmark won't hurt this funciton.
    if (CheckBreakFlag(expr))
        return false;
    if (isa<BinaryOperator>(expr))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
        if (binop->getOpcode() != BO_Assign)
        {
            if (binop->getOpcode() == BO_EQ || binop->getOpcode() == BO_NE || binop->getOpcode() == BO_LT || binop->getOpcode() == BO_GT || binop->getOpcode() == BO_GE || binop->getOpcode() == BO_LE)
            {
                // outs() << "\n[check_guard info] The Expr " << PrintExpr(expr) << " is guard";
                return true;
            }
            else
            {
                // outs() << "\n[check_guard info] The Expr " << PrintExpr(expr) << " is not guard";
                return false;
            }
        }
        else
        {
            // outs() << "\n[check_guard info] The Expr " << PrintExpr(expr) << " is not guard";
            return false;
        }
    }
    else
    {
        // outs() << "\n[check_guard warning] The Unexpected Expr type " << PrintExpr(expr) << "";
        return false;
    }
}

Expr *Trans_LinExpr_to_Expr(Linear_Expression *linExpr, string eliminate_var)
{
    Expr *res = NULL;
    for (int i = 0; i < info->getDim(); i++)
    {
        string var_name = info->get_name(i);
        Expr *rec_expr;
        if (var_name == eliminate_var)
            continue;
        int coef = linExpr->coefficient(Variable(i)).get_si();
        if (coef == 0)
            continue;
        rec_expr = createBinOp(createIntegerLiteral(abs(coef)), createDeclRefExpr(var_name), BO_Mul);
        if (res)
        {
            if (coef < 0)
                res = createBinOp(res, rec_expr, BO_Sub);
            else
                res = createBinOp(res, rec_expr, BO_Add);
        }
        else
        {
            if (coef < 0)
                res = createUnOp(rec_expr, UO_Minus);
            else
                res = rec_expr;
        }
    }
    if (!res)
        res = createIntegerLiteral(0);
    return res;
}

Linear_Expression *Trans_Expr_to_LinExpr(Expr *expr, enum TransformationType type, var_info *total_info)
{
    Linear_Expression *linExpr = new Linear_Expression();
    bool flag = (type == TransformationType::Primed);
    if (isa<BinaryOperator>(expr))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
        if (binop->getOpcode() == BO_Add)
        {
            Linear_Expression *left_expr = Trans_Expr_to_LinExpr(binop->getLHS(), type, total_info);
            Linear_Expression *right_expr = Trans_Expr_to_LinExpr(binop->getRHS(), type, total_info);
            *linExpr = (*left_expr + *right_expr);
        }
        else if (binop->getOpcode() == BO_Sub)
        {
            Linear_Expression *left_expr = Trans_Expr_to_LinExpr(binop->getLHS(), type, total_info);
            Linear_Expression *right_expr = Trans_Expr_to_LinExpr(binop->getRHS(), type, total_info);
            *linExpr = (*left_expr - *right_expr);
        }
        else if (binop->getOpcode() == BO_Mul)
        {
            Linear_Expression *left_expr = Trans_Expr_to_LinExpr(binop->getLHS(), type, total_info);
            Linear_Expression *right_expr = Trans_Expr_to_LinExpr(binop->getRHS(), type, total_info);
            Coefficient coef;
            if (left_expr->space_dimension() == 0)
            {
                coef = left_expr->inhomogeneous_term();
                *linExpr = (coef * (*right_expr));
            }
            else if (right_expr->space_dimension() == 0)
            {
                coef = right_expr->inhomogeneous_term();
                *linExpr = (coef * (*left_expr));
            }
            else
            {
                outs() << "\n[Transform Warning:] Unexpected non-linear expression occur\n"
                       << linExpr;
                exit(-1);
            }
        }
        else
        {
            outs() << "\n[Transform Info:] Unexpected BinaryOperator in Lin_expr:" << binop->getOpcodeStr() << "\n";
            exit(-1);
        }
    }
    else if (isa<DeclRefExpr>(expr))
    {
        DeclRefExpr *decl = dyn_cast<DeclRefExpr>(expr);
        string var_name = decl->getDecl()->getNameAsString();
        int index = total_info->search(var_name.c_str());
        if (flag)
            *linExpr = Variable(index + total_info->getDim());
        else
            *linExpr = Variable(index);
    }
    else if (isa<ParenExpr>(expr))
    {
        ParenExpr *paren = dyn_cast<ParenExpr>(expr);
        linExpr = Trans_Expr_to_LinExpr(paren->getSubExpr(), type, total_info);
    }
    else if (isa<IntegerLiteral>(expr))
    {
        IntegerLiteral *intexpr = dyn_cast<IntegerLiteral>(expr);
        uint64_t value = intexpr->getValue().getLimitedValue();
        if (value <= numeric_limits<int>::max())
        {
            int intValue = static_cast<int>(value);
            *linExpr += intValue;
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
            *linExpr -= *Trans_Expr_to_LinExpr(unop->getSubExpr(), type, total_info);
        }
        else if (unop->getOpcode() == UO_Plus)
        {
            *linExpr += *Trans_Expr_to_LinExpr(unop->getSubExpr(), type, total_info);
        }
        else
        {
            outs() << "\n[Transform Info:] Unexpected UnaryOperator in Lin_expr:" << unop->getOpcodeStr(unop->getOpcode()) << "\n";
        }
    }
    else if (isa<ImplicitCastExpr>(expr))
    {
        ImplicitCastExpr *implict = dyn_cast<ImplicitCastExpr>(expr);
        linExpr = Trans_Expr_to_LinExpr(implict->getSubExpr(), type, total_info);
    }
    else
    {
        outs() << "\n[Transform ToLinExpr Warning:] Unexpected Expression Type: " << expr->getStmtClassName() << "\n";
        outs() << "\n[Warning:] Unexpected Expression: " << PrintExpr(expr) << "\n";
    }
    return linExpr;
}

Expr *Trans_Constraint_to_Expr(Constraint constraint)
{
    // NOTE: Constraint should not contain initial variables
    ASTContext *Context = TransitionSystem::context;
    // Create an Expr for the linear expression part of the constraint.
    Expr *res = nullptr;
    auto linExpr = constraint.expression();
    FPOptions default_options;
    for (int i = 0; i < info->getDim(); i++)
    {
        string name = info->get_name(i);
        int coef = linExpr.coefficient(Variable(i)).get_si();
        if (coef != 0)
        {
            // TODO: only allow unsigned int or unsigned int, special deal with char* or string.
            VarDecl *VD = VarDecl::Create(*Context, Context->getTranslationUnitDecl(), SourceLocation(), SourceLocation(), &Context->Idents.get(name), Context->IntTy, nullptr, SC_None);
            DeclRefExpr *RefExpr = new (Context) DeclRefExpr(*Context, VD, false, VD->getType(), VK_LValue, SourceLocation(), DeclarationNameLoc(), NOUR_None);
            IntegerLiteral *Coef = IntegerLiteral::Create(*Context, APInt(32, abs(coef)), Context->IntTy, SourceLocation());
            BinaryOperator *multExpr = new (Context) BinaryOperator(Coef, RefExpr, BO_Mul, Context->IntTy, VK_RValue, OK_Ordinary, SourceLocation(), default_options);
            if (!res)
            {
                if (coef < 0)
                    res = new (Context) UnaryOperator(multExpr, UO_Minus, Context->IntTy, VK_RValue, OK_Ordinary, SourceLocation(), false);
                else
                    res = multExpr;
            }
            else
            {
                if (coef < 0)
                    res = new (Context) BinaryOperator(res, multExpr, BO_Sub, Context->IntTy, VK_RValue, OK_Ordinary, SourceLocation(), default_options);
                else
                    res = new (Context) BinaryOperator(res, multExpr, BO_Add, Context->IntTy, VK_RValue, OK_Ordinary, SourceLocation(), default_options);
            }
        }
    }

    Coefficient coef = linExpr.inhomogeneous_term();
    int const_term = static_cast<int>(coef.get_si());
    if (const_term != 0)
    {
        IntegerLiteral *Coef = IntegerLiteral::Create(*Context, APInt(32, abs(const_term)), Context->IntTy, SourceLocation());
        if (!res)
        {
            if (const_term < 0)
                res = new (Context) UnaryOperator(Coef, UO_Minus, Context->IntTy, VK_RValue, OK_Ordinary, SourceLocation(), false);
            else
                res = Coef;
        }
        else
        {
            if (const_term < 0)
                res = new (Context) BinaryOperator(res, Coef, BO_Sub, Context->IntTy, VK_RValue, OK_Ordinary, SourceLocation(), default_options);
            else
                res = new (Context) BinaryOperator(res, Coef, BO_Add, Context->IntTy, VK_RValue, OK_Ordinary, SourceLocation(), default_options);
        }
    }

    IntegerLiteral *zero = IntegerLiteral::Create(*Context, APInt(32, 0), Context->IntTy, SourceLocation());
    if (constraint.type() == Constraint::NONSTRICT_INEQUALITY)
    {
        res = new (Context) BinaryOperator(res, zero, BO_GE, Context->IntTy, VK_RValue, OK_Ordinary, SourceLocation(), default_options);
    }
    else if (constraint.type() == Constraint::EQUALITY)
    {
        res = new (Context) BinaryOperator(res, zero, BO_EQ, Context->IntTy, VK_RValue, OK_Ordinary, SourceLocation(), default_options);
    }
    else if (constraint.type() == Constraint::STRICT_INEQUALITY)
    {
        res = new (Context) BinaryOperator(res, zero, BO_GT, Context->IntTy, VK_RValue, OK_Ordinary, SourceLocation(), default_options);
    }

    return res;
}

Constraint_System *TransExprtoConstraints(Expr *expr, enum TransformationType type, var_info *total_info)
{
    // DONE: confirm the expr template, which must be xxx <=/==/>= xxx;
    Constraint_System *constraint = new Constraint_System();
    if (!expr)
        return constraint;
    if (check_guard(expr))
    {
        if (type == TransformationType::Trans)
        {
            type = TransformationType::Origin;
        }
        else if (type == TransformationType::Guard)
        {
            type = TransformationType::Primed;
        }
        else if (type == TransformationType::Loc)
        {
            type = TransformationType::Origin;
        }
        if (isa<BinaryOperator>(expr))
        {
            BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
            if (binop->getOpcode() == BO_EQ)
            {
                Linear_Expression *left_expr = Trans_Expr_to_LinExpr(binop->getLHS(), type, total_info);
                Linear_Expression *right_expr = Trans_Expr_to_LinExpr(binop->getRHS(), type, total_info);
                constraint->insert((*left_expr) == (*right_expr));
            }
            else if (binop->getOpcode() == BO_LT)
            {
                Linear_Expression *left_expr = Trans_Expr_to_LinExpr(binop->getLHS(), type, total_info);
                Linear_Expression *right_expr = Trans_Expr_to_LinExpr(binop->getRHS(), type, total_info);
                constraint->insert((*left_expr) <= (*right_expr - 1));
            }
            else if (binop->getOpcode() == BO_LE)
            {
                Linear_Expression *left_expr = Trans_Expr_to_LinExpr(binop->getLHS(), type, total_info);
                Linear_Expression *right_expr = Trans_Expr_to_LinExpr(binop->getRHS(), type, total_info);
                constraint->insert((*left_expr) <= (*right_expr));
            }
            else if (binop->getOpcode() == BO_GE)
            {
                Linear_Expression *left_expr = Trans_Expr_to_LinExpr(binop->getLHS(), type, total_info);
                Linear_Expression *right_expr = Trans_Expr_to_LinExpr(binop->getRHS(), type, total_info);
                constraint->insert((*left_expr) >= (*right_expr));
            }
            else if (binop->getOpcode() == BO_GT)
            {
                Linear_Expression *left_expr = Trans_Expr_to_LinExpr(binop->getLHS(), type, total_info);
                Linear_Expression *right_expr = Trans_Expr_to_LinExpr(binop->getRHS(), type, total_info);
                constraint->insert((*left_expr - 1) >= (*right_expr));
            }
            else if (binop->getOpcode() == BO_NE)
            {
                Linear_Expression *left_expr = Trans_Expr_to_LinExpr(binop->getLHS(), type, total_info);
                Linear_Expression *right_expr = Trans_Expr_to_LinExpr(binop->getRHS(), type, total_info);
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
            outs() << "\n[Transform unexpected Opcode in Guard Expr type: " << PrintExpr(expr) << "]\n";
        }
        if (isa<BinaryOperator>(expr))
        {
            BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
            if (binop->getOpcode() == BO_Assign)
            {
                VariableInfo var;
                var.assign(binop->getLHS(), binop->getRHS());
                int index = total_info->search(var.getVarName().c_str());
                if (type == TransformationType::Trans)
                    index += total_info->getDim();
                type = TransformationType::Origin;
                Linear_Expression *left_expr = new Linear_Expression(Variable(index));
                Linear_Expression *right_expr = Trans_Expr_to_LinExpr(binop->getRHS(), type, total_info);
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

bool TraverseExprForVar(Expr *expr, string var_name)
{
    if (!expr)
        return false;
    if (CheckBreakFlag(expr))
        return true;
    bool flag = false;
    if (isa<BinaryOperator>(expr))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
        flag |= TraverseExprForVar(binop->getLHS(), var_name);
        flag |= TraverseExprForVar(binop->getRHS(), var_name);
    }
    else if (isa<DeclRefExpr>(expr))
    {
        DeclRefExpr *declRef = dyn_cast<DeclRefExpr>(expr);
        string name = declRef->getDecl()->getNameAsString();
        if (name.find(INITSUFFIX) != name.npos)
        {
            int index = name.find(INITSUFFIX);
            name.replace(index, strlen(INITSUFFIX), "");
        }
        if (name == var_name)
            return true;
        else
            return false;
    }
    else if (isa<ImplicitCastExpr>(expr))
    {
        ImplicitCastExpr *implict = dyn_cast<ImplicitCastExpr>(expr);
        flag |= TraverseExprForVar(implict->getSubExpr(), var_name);
    }
    else if (isa<IntegerLiteral>(expr))
    {
    }
    else if (isa<UnaryOperator>(expr))
    {
        UnaryOperator *unop = dyn_cast<UnaryOperator>(expr);
        flag |= TraverseExprForVar(unop->getSubExpr(), var_name);
    }
    else if (isa<ParenExpr>(expr))
    {
        ParenExpr *paren = dyn_cast<ParenExpr>(expr);
        flag |= TraverseExprForVar(paren->getSubExpr(), var_name);
    }
    else
    {
        LOGINFO("Unexpected Type in Function TraverseExprForVars :");
        LOGINFO(PrintExpr(expr));
        exit(-1);
    }
    return flag;
}

bool TraverseExprCheckVar(Expr *expr, const unordered_set<string> &res)
{
    if (CheckBreakFlag(expr))
        return true;
    bool flag = false;
    if (isa<BinaryOperator>(expr))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
        flag |= TraverseExprCheckVar(binop->getLHS(), res);
        flag |= TraverseExprCheckVar(binop->getRHS(), res);
    }
    else if (isa<DeclRefExpr>(expr))
    {
        DeclRefExpr *declRef = dyn_cast<DeclRefExpr>(expr);
        string name = declRef->getDecl()->getNameAsString();
        if (name.find(INITSUFFIX) != name.npos)
        {
            int index = name.find(INITSUFFIX);
            name.replace(index, strlen(INITSUFFIX), "");
        }
        if (res.find(name) != res.end())
            return true;
        else
            return false;
    }
    else if (isa<ImplicitCastExpr>(expr))
    {
        ImplicitCastExpr *implict = dyn_cast<ImplicitCastExpr>(expr);
        flag |= TraverseExprCheckVar(implict->getSubExpr(), res);
    }
    else if (isa<IntegerLiteral>(expr))
    {
    }
    else if (isa<UnaryOperator>(expr))
    {
        UnaryOperator *unop = dyn_cast<UnaryOperator>(expr);
        flag |= TraverseExprCheckVar(unop->getSubExpr(), res);
    }
    else if (isa<ParenExpr>(expr))
    {
        ParenExpr *paren = dyn_cast<ParenExpr>(expr);
        flag |= TraverseExprCheckVar(paren->getSubExpr(), res);
    }
    else
    {
        LOGINFO("Unexpected Type in Function TraverseExprForVars :");
        LOGINFO(PrintExpr(expr));
        exit(-1);
    }
    return flag;
}

bool TraverseExprCheckVars(Expr *expr, const unordered_set<string> &res)
{
    if (CheckBreakFlag(expr))
        return true;
    bool flag = true;
    if (isa<BinaryOperator>(expr))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
        flag &= TraverseExprCheckVars(binop->getLHS(), res);
        flag &= TraverseExprCheckVars(binop->getRHS(), res);
    }
    else if (isa<DeclRefExpr>(expr))
    {
        DeclRefExpr *declRef = dyn_cast<DeclRefExpr>(expr);
        string name = declRef->getDecl()->getNameAsString();
        if (name.find(INITSUFFIX) != name.npos)
        {
            int index = name.find(INITSUFFIX);
            name.replace(index, strlen(INITSUFFIX), "");
        }
        if (res.find(name) != res.end())
            return true;
        else
            return false;
    }
    else if (isa<ImplicitCastExpr>(expr))
    {
        ImplicitCastExpr *implict = dyn_cast<ImplicitCastExpr>(expr);
        flag &= TraverseExprCheckVars(implict->getSubExpr(), res);
    }
    else if (isa<IntegerLiteral>(expr))
    {
    }
    else if (isa<UnaryOperator>(expr))
    {
        UnaryOperator *unop = dyn_cast<UnaryOperator>(expr);
        flag &= TraverseExprCheckVars(unop->getSubExpr(), res);
    }
    else if (isa<ParenExpr>(expr))
    {
        ParenExpr *paren = dyn_cast<ParenExpr>(expr);
        flag &= TraverseExprCheckVars(paren->getSubExpr(), res);
    }
    else
    {
        LOGINFO("Unexpected Type in Function TraverseExprForVars :");
        LOGINFO(PrintExpr(expr));
        exit(-1);
    }
    return flag;
}

void TraverseExprForVars(Expr *expr, unordered_set<string> &res)
{
    if (!expr)
        return;
    if (CheckBreakFlag(expr))
        return;
    if (isa<BinaryOperator>(expr))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
        TraverseExprForVars(binop->getLHS(), res);
        TraverseExprForVars(binop->getRHS(), res);
    }
    else if (isa<DeclRefExpr>(expr))
    {
        DeclRefExpr *declRef = dyn_cast<DeclRefExpr>(expr);
        string name = declRef->getDecl()->getNameAsString();
        if (name.find(INITSUFFIX) != name.npos)
        {
            int index = name.find(INITSUFFIX);
            name.replace(index, strlen(INITSUFFIX), "");
        }
        res.insert(name);
    }
    else if (isa<ImplicitCastExpr>(expr))
    {
        ImplicitCastExpr *implict = dyn_cast<ImplicitCastExpr>(expr);
        TraverseExprForVars(implict->getSubExpr(), res);
    }
    else if (isa<IntegerLiteral>(expr))
    {
        return;
    }
    else if (isa<UnaryOperator>(expr))
    {
        UnaryOperator *unop = dyn_cast<UnaryOperator>(expr);
        TraverseExprForVars(unop->getSubExpr(), res);
    }
    else if (isa<ParenExpr>(expr))
    {
        ParenExpr *paren = dyn_cast<ParenExpr>(expr);
        TraverseExprForVars(paren->getSubExpr(), res);
    }
    else if (isa<CallExpr>(expr))
    {
        CallExpr *call = dyn_cast<CallExpr>(expr);
        for (int index = 0; index < call->getNumArgs(); index++)
        {
            Expr *call_param = call->getArg(index);
            TraverseExprForVars(call_param, res);
        }
    }
    else
    {
        LOGWARN("Unexpected Type " + string(expr->getStmtClassName()));
        LOGWARN(PrintExpr(expr));
        exit(-1);
    }
    return;
}
bool CheckInitSuffix(Expr *expr)
{
    if (isa<BinaryOperator>(expr))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
        bool flag = false;
        flag |= CheckInitSuffix(binop->getLHS());
        flag |= CheckInitSuffix(binop->getRHS());
        return flag;
    }
    else if (isa<DeclRefExpr>(expr))
    {
        DeclRefExpr *declRef = dyn_cast<DeclRefExpr>(expr);
        string name = declRef->getDecl()->getNameAsString();
        if (name.find(INITSUFFIX) != name.npos)
            return true;
        else
            return false;
    }
    else if (isa<ImplicitCastExpr>(expr))
    {
        ImplicitCastExpr *implict = dyn_cast<ImplicitCastExpr>(expr);
        return CheckInitSuffix(implict->getSubExpr());
    }
    else if (isa<IntegerLiteral>(expr))
    {
    }
    else if (isa<UnaryOperator>(expr))
    {
        UnaryOperator *unop = dyn_cast<UnaryOperator>(expr);
        return CheckInitSuffix(unop->getSubExpr());
    }
    else
    {
        LOGWARN("Unexpected Type" + string(expr->getStmtClassName()));
        LOGWARN(PrintExpr(expr));
        exit(-1);
    }
    return false;
}
Expr *Add_InitSuffix(Expr *expr)
{
    if (isa<BinaryOperator>(expr))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
        binop->setLHS(Add_InitSuffix(binop->getLHS()));
        binop->setRHS(Add_InitSuffix(binop->getRHS()));
        return binop;
    }
    else if (isa<DeclRefExpr>(expr))
    {
        DeclRefExpr *declRef = dyn_cast<DeclRefExpr>(expr);
        VarDecl *VD;
        ASTContext *context = TransitionSystem::context;
        VD = VarDecl::Create(*context, context->getTranslationUnitDecl(), SourceLocation(), SourceLocation(), &context->Idents.get((declRef->getDecl()->getNameAsString() + INITSUFFIX)), declRef->getType(), nullptr, SC_None);
        declRef = new (context) DeclRefExpr(*context, VD, false, VD->getType(), VK_LValue, SourceLocation(), DeclarationNameLoc(), NOUR_None);
        return declRef;
    }
    else if (isa<ImplicitCastExpr>(expr))
    {
        ImplicitCastExpr *implict = dyn_cast<ImplicitCastExpr>(expr);
        implict->setSubExpr(Add_InitSuffix(implict->getSubExpr()));
        return implict;
    }
    else if (isa<IntegerLiteral>(expr))
    {
        return expr;
    }
    else if (isa<UnaryOperator>(expr))
    {
        UnaryOperator *unop = dyn_cast<UnaryOperator>(expr);
        unop->setSubExpr(Add_InitSuffix(unop->getSubExpr()));
        return unop;
    }
    else
    {
        LOGWARN("Unexpected Type" + string(expr->getStmtClassName()));
        LOGWARN(PrintExpr(expr));
        exit(-1);
    }
    return expr;
}

Expr *eliminate_initsuffix(Expr *expr)
{
    if (isa<BinaryOperator>(expr))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
        binop->setLHS(eliminate_initsuffix(binop->getLHS()));
        binop->setRHS(eliminate_initsuffix(binop->getRHS()));
        return binop;
    }
    else if (isa<DeclRefExpr>(expr))
    {
        DeclRefExpr *declRef = dyn_cast<DeclRefExpr>(expr);
        VarDecl *VD;
        ASTContext *context = TransitionSystem::context;
        string name = declRef->getDecl()->getNameAsString();
        if (name.find(INITSUFFIX) != name.npos)
            name.replace(name.find(INITSUFFIX), strlen(INITSUFFIX), "");
        VD = VarDecl::Create(*context, context->getTranslationUnitDecl(), SourceLocation(), SourceLocation(), &context->Idents.get(name), declRef->getType(), nullptr, SC_None);
        declRef = new (context) DeclRefExpr(*context, VD, false, VD->getType(), VK_LValue, SourceLocation(), DeclarationNameLoc(), NOUR_None);
        return declRef;
    }
    else if (isa<ImplicitCastExpr>(expr))
    {
        ImplicitCastExpr *implict = dyn_cast<ImplicitCastExpr>(expr);
        implict->setSubExpr(eliminate_initsuffix(implict->getSubExpr()));
        return implict;
    }
    else if (isa<UnaryOperator>(expr))
    {
        UnaryOperator *unop = dyn_cast<UnaryOperator>(expr);
        unop->setSubExpr(eliminate_initsuffix(unop->getSubExpr()));
        return unop;
    }
    else if (isa<IntegerLiteral>(expr))
    {
    }
    else
    {
        LOGWARN("Unexpected Type" + string(expr->getStmtClassName()));
        LOGWARN(PrintExpr(expr));
        exit(-1);
    }
    return expr;
}
vector<C_Polyhedron> ComputeInitPolys(unordered_set<string> &total_vars, Expr *condition, vector<vector<Expr *>> &InitDNF, vector<vector<Expr *>> &InitIneqDNF, vector<vector<VariableInfo>> &InitVars, var_info *total_info)
{
    // TODO: deal with the situation that return size=0;
    // DONE: write the transformation from Constraint to Expression.
    // DONE: think the inequality init_value.
    vector<vector<Expr *>> DNF;
    ASTContext *context = TransitionSystem::context;
    DNF.resize(InitDNF.size());
    assert(InitDNF.size() == InitVars.size());

    for (int i = 0; i < InitDNF.size(); i++)
    {
        unordered_set<string> rec_used;
        for (int j = 0; j < InitVars[i].size(); j++)
        {
            string var_name = InitVars[i][j].getVarName();
            if (TraverseExprForVar(InitVars[i][j].getVarValue(), var_name))
            {
                rec_used.insert(var_name);
            }
        }
        for (auto name : total_vars)
        {
            if (rec_used.count(name) == 0)
            {
                DeclRefExpr *left = createDeclRefExpr(name);
                DeclRefExpr *right = createDeclRefExpr(name + INITSUFFIX);
                BinaryOperator *assign = createBinOp(left, right, BO_Assign);
                DNF[i].push_back(assign);
            }
        }
    }
    for (int i = 0; i < InitDNF.size(); i++)
    {
        for (int j = 0; j < InitDNF[i].size(); j++)
        {
            if (TraverseExprCheckVars(InitDNF[i][j], total_vars))
            {
                if (!isa<BinaryOperator>(InitDNF[i][j]))
                {
                    LOGWARN("Unexpected type of InitDNF.");
                    exit(-1);
                }
                DNF[i].push_back(InitDNF[i][j]);
                InitDNF[i].erase(InitDNF[i].begin() + j);
                j--;
            }
        }
    }

    vector<vector<Expr *>> RecIneqDNF;
    RecIneqDNF.resize(InitIneqDNF.size());
    for (int i = 0; i < InitIneqDNF.size(); i++)
    {
        for (int j = 0; j < InitIneqDNF[i].size(); j++)
        {
            if (TraverseExprCheckVars(InitIneqDNF[i][j], total_vars))
            {
                RecIneqDNF[i].push_back(InitIneqDNF[i][j]);
                InitIneqDNF[i].erase(InitIneqDNF[i].begin() + j);
                j--;
            }
        }
    }
    for (int i = 0; i < RecIneqDNF.size(); i++)
    {
        for (int j = 0; j < RecIneqDNF[i].size(); j++)
        {
            if (CheckBreakFlag(RecIneqDNF[i][j]))
                continue;
            if (!CheckInitSuffix(RecIneqDNF[i][j]))
                RecIneqDNF[i][j] = Add_InitSuffix(RecIneqDNF[i][j]);
        }
    }
    DNF = AppendDNF(DNF, RecIneqDNF);
    LOGINFO("Before Transform InitDNF into polyhedron: ");
    PrintDNF(DNF);
    vector<C_Polyhedron> init_polys;
    for (int i = 0; i < DNF.size(); i++)
    {
        C_Polyhedron *p = new C_Polyhedron(total_info->getDim(), UNIVERSE);
        for (int j = 0; j < DNF[i].size(); j++)
        {
            if (CheckBreakFlag(DNF[i][j]))
                continue;
            p->add_constraints(*TransExprtoConstraints(DNF[i][j], TransformationType::Loc, total_info));
        }
        if (!p->is_empty())
            init_polys.push_back(*p);
    }
    for (int i = 0; i < DNF.size(); i++)
    {
        for (int j = 0; j < DNF[i].size(); j++)
        {
            if (CheckBreakFlag(DNF[i][j]))
                continue;
            eliminate_initsuffix(DNF[i][j]);
        }
    }
    return init_polys;
}

Expr *NegateExpr(Expr *expr)
{
    ASTContext *context = TransitionSystem::context;
    UnaryOperator *notExpr = new (context) UnaryOperator(expr, UO_LNot, context->BoolTy, VK_RValue, OK_Ordinary, SourceLocation(), false);
    return notExpr;
}

void TransitionSystem::AddComment(ACSLComment *comment)
{
    comments.push_back(comment);
    return;
}

void TransitionSystem::AddVars(VariableInfo &var)
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

void TransitionSystem::AddVars(VariableInfo &var, Expr *expr)
{
    if (Vars.size() == 0)
    {
        Vars.resize(1);
    }

    for (int i = 0; i < Vars.size(); i++)
    {
        var.assign("", TransExprbyCurVars(expr, Vars[i]), var.getQualType());
        VariableInfo::search_and_insert(var, Vars[i]);
    }
    return;
}

void TransitionSystem::AddFundExpr(unordered_set<string> &UsedVars)
{
    for (int i = 0; i < DNF.size(); i++)
    {
        unordered_set<string> rec_used;
        for (int j = 0; j < DNF[i].size(); j++)
        {
            if (CheckBreakFlag(DNF[i][j]))
                continue;
            if (isa<BinaryOperator>(DNF[i][j]))
            {
                BinaryOperator *binop = dyn_cast<BinaryOperator>(DNF[i][j]);
                if (binop->getOpcode() != BO_Assign)
                {
                    LOGWARN("Invalid DNF type: " + string(DNF[i][j]->getStmtClassName()));
                    exit(-1);
                }
                DeclRefExpr *decl = dyn_cast<DeclRefExpr>(binop->getLHS());
                rec_used.insert(decl->getDecl()->getNameAsString());
            }
            else
            {
                LOGWARN("Invalid DNF type: " + string(DNF[i][j]->getStmtClassName()));
                exit(-1);
            }
        }
        for (const auto &name : UsedVars)
        {
            FPOptions default_options;
            if (rec_used.count(name) == 0)
            {
                DeclRefExpr *decl_left = createDeclRefExpr(name);
                DeclRefExpr *decl_right = createDeclRefExpr(name);
                BinaryOperator *assign = new (context) BinaryOperator(decl_left, decl_right, BO_Assign, context->IntTy, VK_RValue, OK_Ordinary, SourceLocation(), default_options);
                DNF[i].push_back(assign);
            }
            DeclRefExpr *decl_left = createDeclRefExpr(name + INITSUFFIX);
            DeclRefExpr *decl_right = createDeclRefExpr(name + INITSUFFIX);
            BinaryOperator *assign = new (context) BinaryOperator(decl_left, decl_right, BO_Assign, context->IntTy, VK_RValue, OK_Ordinary, SourceLocation(), default_options);
            DNF[i].push_back(assign);
        }
    }
}

void TransitionSystem::AddFundInitexpr(unordered_set<string> &UsedVars, vector<vector<Expr *>> &dnf)
{
    assert(Vars.size() == dnf.size());
    for (int i = 0; i < Vars.size(); i++)
    {
        unordered_set<string> rec_used;
        for (int j = 0; j < Vars[i].size(); j++)
        {
            string var_name = Vars[i][j].getVarName();
            if (var_name == "")
                continue;
            if (TraverseExprForVar(Vars[i][j].getVarValue(), var_name))
            {
                rec_used.insert(var_name);
            }
        }
        for (auto name : UsedVars)
        {
            if (name == "")
                continue;
            if (rec_used.count(name) == 0)
            {
                DeclRefExpr *left = createDeclRefExpr(name);
                DeclRefExpr *right = createDeclRefExpr(name + INITSUFFIX);
                BinaryOperator *assign = createBinOp(left, right, BO_Assign);
                dnf[i].push_back(assign);
            }
        }
    }
}

void TransitionSystem::AddExpr(Expr *expr)
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

unordered_set<string> TransitionSystem::MergeFuncCall(vector<vector<Expr *>> &function_dnf, CallExpr *callexpr, string new_return_name, unordered_set<string> global_vars)
{
    vector<vector<Expr *>> fDNF;
    vector<vector<Expr *>> fIneqDNF;
    unordered_set<string> non_LocalVars;
    unordered_set<string> rec_vars;
    unordered_set<string> LocalVars;
    FunctionDecl *func = callexpr->getDirectCallee();
    string return_name = func->getNameAsString() + "_RetVal";
    non_LocalVars.insert(new_return_name);
    non_LocalVars.insert(global_vars.begin(), global_vars.end());
    int size = function_dnf.size();
    vector<vector<Expr *>> new_DNF;
    vector<vector<Expr *>> new_ineqDNF;

    // NOTE: default args forbidden;
    assert(func->getNumParams() == callexpr->getNumArgs());
    for (int index = 0; index < callexpr->getNumArgs(); index++)
    {
        Expr *call_param = callexpr->getArg(index);
        string call_name;
        ParmVarDecl *param = func->getParamDecl(index);
        if (isa<ImplicitCastExpr>(call_param))
            call_param = (dyn_cast<ImplicitCastExpr>(call_param))->getSubExpr();
        if (isa<UnaryOperator>(call_param))
        {
            UnaryOperator *unop = dyn_cast<UnaryOperator>(call_param);
            Expr *subexpr = unop->getSubExpr();
            if (isa<DeclRefExpr>(subexpr))
            {
                DeclRefExpr *decl = dyn_cast<DeclRefExpr>(subexpr);
                call_name = decl->getDecl()->getNameAsString();
            }
            else
            {
                LOGWARN("unexpected type: " + string(subexpr->getStmtClassName()));
            }
            if (unop->getOpcode() == UO_AddrOf)
            {
                string origin_name = "*" + param->getNameAsString();
                non_LocalVars.insert(call_name);
                for (int i = 0; i < function_dnf.size(); i++)
                {
                    for (int j = 0; j < function_dnf[i].size(); j++)
                    {
                        function_dnf[i][j] = ReplaceExprForVar(function_dnf[i][j], origin_name, call_name);
                    }
                }
                continue;
            }
        }
        else if (isa<DeclRefExpr>(call_param))
        {
            DeclRefExpr *decl = dyn_cast<DeclRefExpr>(call_param);
            call_name = decl->getDecl()->getNameAsString();
        }
        else
        {
            LOGINFO("cannot deal with expression in callfunction param");
            exit(1);
        }
        QualType type = param->getType();
        if (param->getNameAsString() == call_name)
            continue;
        if (type->isPointerType())
        {
            for (int i = 0; i < function_dnf.size(); i++)
            {
                for (int j = 0; j < function_dnf[i].size(); j++)
                {
                    function_dnf[i][j] = ReplaceExprForVar(function_dnf[i][j], "*" + param->getNameAsString(), "*" + call_name);
                    non_LocalVars.insert("*" + call_name);
                }
            }
        }
        else
        {
            for (int i = 0; i < function_dnf.size(); i++)
            {
                for (int j = 0; j < function_dnf[i].size(); j++)
                {
                    function_dnf[i][j] = ReplaceExprForVar(function_dnf[i][j], param->getNameAsString(), call_name);
                }
            }
        }
    }
    for (int i = 0; i < function_dnf.size(); i++)
    {
        for (int j = 0; j < function_dnf[i].size(); j++)
        {
            if (isa<DeclRefExpr>(function_dnf[i][j]))
                continue;
            function_dnf[i][j] = ReplaceExprForVar(function_dnf[i][j], return_name, new_return_name);

            TraverseExprForVars(function_dnf[i][j], rec_vars);
            for (auto name : rec_vars)
            {
                if (non_LocalVars.count(name) == 0)
                {
                    function_dnf[i][j] = ReplaceExprForVar(function_dnf[i][j], name, name + "_" + func->getNameAsString());
                    LocalVars.insert(name + "_" + func->getNameAsString());
                }
            }
        }
    }
    TransitionSystem res;
    vector<ACSLComment *> rec_comments = getComments();
    for (int i = 0; i < function_dnf.size(); i++)
    {
        TransitionSystem rec_transystem(*this);
        for (int j = 0; j < function_dnf[i].size(); j++)
        {
            Expr *expr = function_dnf[i][j];
            if (isa<DeclRefExpr>(expr))
                continue;

            if (isa<BinaryOperator>(expr))
            {
                BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);

                if (binop->getOpcode() == BO_Assign)
                {
                    VariableInfo var;
                    Expr *expr = binop->getLHS();
                    DeclRefExpr *decl = dyn_cast<DeclRefExpr>(expr);
                    var.assign(binop->getLHS(), NULL);
                    rec_transystem.AddVars(var, binop->getRHS());
                }
                else
                {
                    for (int k = 0; k < rec_transystem.Vars.size(); k++)
                    {
                        expr = TransExprbyCurVars(expr, rec_transystem.Vars[k]);
                        rec_transystem.InequalityDNF[k].push_back(expr);
                    }
                }
            }
            else
            {
                LOGWARN("Unexpected Expr Type: " + string(expr->getStmtClassName()));
                exit(-1);
            }
        }
        res = MergeTransystem(res, rec_transystem);
    }
    *this = res;
    MergeComments(rec_comments);
    return LocalVars;
}

void TransitionSystem::MergeIneqDNF(vector<vector<Expr *>> &dnf)
{
    InequalityDNF = Merge_DNF(InequalityDNF, dnf);
    CopyAfterUpdate(dnf.size());
    return;
}

// void TransitionSystem::recover_dnf(vector<vector<Expr *>> &dnf)
// {
//     assert(Graphs.size() == dnf.size());
//     for (int i = 0; i < dnf.size(); i++)
//     {
//         map<string, unordered_set<string>> possibles = Graphs[i].possible_rv;
//         vector<string> node;
//         for (const auto &pair : possibles)
//             node.push_back(pair.first);
//         for (auto name : node)
//             LOGINFO(name);
//         for (int j = 0; j < dnf[i].size(); j++)
//         {
//             Expr *expr = dnf[i][j];
//             if (!isa<BinaryOperator>(expr))
//             {
//                 LOGWARN("Unexpected Expr Type: " + string(expr->getStmtClassName()));
//                 exit(-1);
//             }
//             BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
//             if (binop->getOpcode() != BO_EQ)
//                 continue;
//             int count = 0;
//             string rec_name;
//             for (const auto &name : node)
//             {
//                 if (TraverseExprCheckVars(expr, possibles[name]))
//                 {
//                     count++;
//                     rec_name = name;
//                 }
//             }
//             if (count == 1)
//             {
//                 DeclRefExpr *left = createDeclRefExpr(rec_name);
//                 Expr *right_expr = Trans_LinExpr_to_Expr(Trans_Expr_to_LinExpr(binop->getLHS(), TransformationType::Loc, info->getDim()), rec_name);
//                 dnf[i][j] = createBinOp(left, right_expr, BO_Assign);
//             }
//             else if (count > 1)
//             {
//                 // TODO : Deal the different order, which possibly leads to such issues
//                 LOGWARN("Unexpected Situtation While possible left value count >=2");
//                 exit(-1);
//             }
//         }
//     }
// }

Expr *TransitionSystem::TransVartoExpr(VariableInfo var, bool init)
{
    // assert(var.getQualType().getAsString()=="int");
    Expr *initExpr = var.getVarValue();
    string var_name = var.getVarName();
    if (initExpr == NULL)
    {
        return NULL;
    }
    if (init)
    {
        initExpr = Add_InitSuffix(initExpr);
    }
    DeclRefExpr *LHS = createDeclRefExpr(var_name);
    FPOptions default_options;
    BinaryOperator *binop = createBinOp(LHS, initExpr, BO_Assign);
    return binop;
}
vector<vector<Expr *>> TransPolystoExprs(vector<C_Polyhedron *> poly, bool init_remove)
{
    vector<vector<Expr *>> res;
    for (int i = 0; i < poly.size(); i++)
    {
        C_Polyhedron *rec_poly = poly[i];
        vector<Expr *> exprs;
        if (init_remove)
        {
            Variables_Set rec_set;
            for (int i = 0; i < info->getDim(); i++)
            {
                string name = info->get_name(i);
                if (name.find(INITSUFFIX) != name.npos)
                    rec_set.insert(Variable(i));
            }
            rec_poly->remove_space_dimensions(rec_set);
        }
        for (auto constraint : rec_poly->minimized_constraints())
        {
            exprs.push_back(Trans_Constraint_to_Expr(constraint));
        }
        res.push_back(exprs);
    }
    for (int i = 0; i < res.size(); i++)
    {
        if (res[i].size() == 0)
        {
            res.erase(res.begin() + i);
            i--;
        }
    }
    return res;
}
vector<vector<Expr *>> TransPolystoExprs(vector<C_Polyhedron> poly, bool init_remove)
{
    vector<vector<Expr *>> res;
    for (int i = 0; i < poly.size(); i++)
    {
        C_Polyhedron rec_poly = poly[i];
        vector<Expr *> exprs;
        if (init_remove)
        {
            Variables_Set rec_set;
            for (int i = 0; i < info->getDim(); i++)
            {
                string name = info->get_name(i);
                if (name.find(INITSUFFIX) != name.npos)
                    rec_set.insert(Variable(i));
            }
            rec_poly.remove_space_dimensions(rec_set);
        }
        for (auto constraint : rec_poly.minimized_constraints())
        {
            exprs.push_back(Trans_Constraint_to_Expr(constraint));
        }
        res.push_back(exprs);
    }
    for (int i = 0; i < res.size(); i++)
    {
        if (res[i].size() == 0)
        {
            res.erase(res.begin() + i);
            i--;
        }
    }
    return res;
}

void TransitionSystem::InLoop()
{
    InWhileLoop = true;
    DNF.clear();
    Vars.clear();
    InequalityDNF.clear();
    DNF.resize(1);
    Vars.resize(1);
    InequalityDNF.resize(1);
    return;
}

unordered_set<string> TransitionSystem::getUsedVars(Expr *cond, Expr *increment)
{
    unordered_set<string> UsedVars;
    for (int i = 0; i < DNF.size(); i++)
    {
        for (int j = 0; j < DNF[i].size(); j++)
        {
            TraverseExprForVars(DNF[i][j], UsedVars);
        }
    }
    for (int i = 0; i < InequalityDNF.size(); i++)
    {
        for (int j = 0; j < InequalityDNF[i].size(); j++)
        {
            TraverseExprForVars(InequalityDNF[i][j], UsedVars);
        }
    }
    TraverseExprForVars(cond, UsedVars);
    TraverseExprForVars(increment, UsedVars);
    return UsedVars;
}

void TransitionSystem::CopyAfterUpdate(int size)
{
    int duplicated = DNF.size();
    for (int i = 0; i < size - 1; i++)
    {
        for (int j = 0; j < duplicated; j++)
        {
            Vars.push_back(Vars[j]);
            DNF.push_back(DNF[j]);
        }
    }
    return;
}

void TransitionSystem::MergeComments(vector<ACSLComment *> &comment)
{
    comments.insert(comments.end(), comment.begin(), comment.end());
    return;
}
void TransitionSystem::MergeCond(Expr *condition, bool updated)
{
    vector<vector<Expr *>> exprs;
    exprs = DealwithCond(condition, true, exprs);
    CopyAfterUpdate(exprs.size());
    if (!updated)
    {
        vector<vector<Expr *>> new_inequailty_dnf;
        for (int i = 0; i < exprs.size(); i++)
        {
            for (int j = 0; j < InequalityDNF.size(); j++)
            {
                vector<Expr *> rec_dnf;
                rec_dnf.insert(rec_dnf.end(), InequalityDNF[j].begin(), InequalityDNF[j].end());
                for (int k = 0; k < exprs[i].size(); k++)
                {
                    rec_dnf.push_back(TransExprbyCurVars(exprs[i][k], Vars[j]));
                }
                new_inequailty_dnf.push_back(rec_dnf);
            }
        }
        InequalityDNF = new_inequailty_dnf;
    }
    else
        InequalityDNF = Merge_DNF(InequalityDNF, exprs);
    return;
}

TransitionSystem TransitionSystem::MergeTransystem(TransitionSystem &left_trans, TransitionSystem &right_trans)
{
    // TODO: consider the situation of nested loop.
    TransitionSystem transystem;
    transystem.InequalityDNF = ConnectDNF(left_trans.InequalityDNF, right_trans.InequalityDNF);
    transystem.DNF = ConnectDNF(left_trans.DNF, right_trans.DNF);
    for (int i = 0; i < left_trans.comments.size(); i++)
        transystem.comments.push_back(left_trans.comments[i]);
    for (int i = 0; i < right_trans.comments.size(); i++)
        transystem.comments.push_back(right_trans.comments[i]);
    for (int i = 0; i < left_trans.Vars.size(); i++)
        transystem.Vars.push_back(left_trans.Vars[i]);
    for (int i = 0; i < right_trans.Vars.size(); i++)
        transystem.Vars.push_back(right_trans.Vars[i]);
    transystem.Verified_Loop_Count = left_trans.Verified_Loop_Count + right_trans.Verified_Loop_Count;
    return transystem;
}

void TransitionSystem::delete_expr_by_var(string var_name)
{
    unordered_set<string> UsedVars;
    UsedVars.insert(var_name);
    for (int i = 0; i < DNF.size(); i++)
    {
        for (int j = 0; j < DNF[i].size(); j++)
        {
            if (TraverseExprCheckVar(DNF[i][j], UsedVars))
            {
                DNF[i].erase(DNF[i].begin() + j);
                j--;
            }
        }
    }
    for (int i = 0; i < InequalityDNF.size(); i++)
    {
        for (int j = 0; j < InequalityDNF[i].size(); j++)
        {
            if (TraverseExprCheckVar(InequalityDNF[i][j], UsedVars))
            {
                InequalityDNF[i].erase(InequalityDNF[i].begin() + j);
                j--;
            }
        }
    }
    return;
}
void TransitionSystem::UpdateVars(bool init)
{
    if (DNF.size() != Vars.size())
    {
        LOGWARN("Unexpected size of DNF and Vars: " + to_string(DNF.size()) + " and " + to_string(Vars.size()));
        exit(-1);
    }
    for (int i = 0; i < Vars.size(); i++)
    {
        for (int j = 0; j < Vars[i].size(); j++)
        {
            Expr *assign_expr;
            assign_expr = TransVartoExpr(Vars[i][j], init);
            if (assign_expr)
                DNF[i].push_back(assign_expr);
        }
    }
    return;
}

void TransitionSystem::deduplicate(vector<vector<Expr *>> &dnf)
{
    unordered_set<string> UsedVars;
    for (int i = 0; i < dnf.size(); i++)
    {
        for (int j = 0; j < dnf[i].size(); j++)
        {
            TraverseExprForVars(dnf[i][j], UsedVars);
        }
    }
    var_info *rec_info = new var_info(info);
    if (!info)
        rec_info = NULL;
    info = new var_info();
    for (auto name : UsedVars)
    {
        info->insert(name.c_str());
        info->insert((name + INITSUFFIX).c_str());
    }
    PrintDNF(dnf);
    for (int i = 0; i < dnf.size(); i++)
    {
        C_Polyhedron *p = new C_Polyhedron(info->getDim(), UNIVERSE);
        for (int j = 0; j < dnf[i].size(); j++)
        {
            LOGINFO(PrintExpr(dnf[i][j]));
            p->add_constraints(*TransExprtoConstraints(dnf[i][j], TransformationType::Loc, info));
        }
        if (p->is_empty())
        {
            dnf.erase(dnf.begin() + i);
            i--;
        }
    }
    delete info;
    info = rec_info;
    return;
}
vector<vector<Expr *>> TransitionSystem::DealwithCond(Expr *condition, bool logic)
{
    vector<vector<Expr *>> cur;
    return DealwithCond(condition, logic, cur);
}

vector<vector<Expr *>> TransitionSystem::DealwithCond(Expr *condition, bool logic, vector<vector<Expr *>> cur)
{
    vector<vector<Expr *>> left_expr;
    vector<vector<Expr *>> right_expr;
    FPOptions default_options;
    if (BinaryOperator *binop = dyn_cast<BinaryOperator>(condition))
    {
        if (binop->getOpcode() == BO_LAnd)
        {
            if (logic)
            {
                left_expr = DealwithCond(binop->getLHS(), logic, cur);
                right_expr = DealwithCond(binop->getRHS(), logic, cur);
                return Merge_DNF(left_expr, right_expr);
            }
            else
            {
                left_expr = DealwithCond(binop->getLHS(), logic, cur);
                right_expr = DealwithCond(binop->getRHS(), logic, cur);
                return ConnectDNF(left_expr, right_expr);
            }
        }
        else if (binop->getOpcode() == BO_LOr)
        {
            if (!logic)
            {
                left_expr = DealwithCond(binop->getLHS(), logic, cur);
                right_expr = DealwithCond(binop->getRHS(), logic, cur);
                return Merge_DNF(left_expr, right_expr);
            }
            else
            {
                left_expr = DealwithCond(binop->getLHS(), logic, cur);
                right_expr = DealwithCond(binop->getRHS(), logic, cur);
                return ConnectDNF(left_expr, right_expr);
            }
        }
        else if (binop->getOpcode() == BO_NE)
        {
            if (logic)
            {
                BinaryOperator *binop_left = new (context) BinaryOperator(binop->getLHS(), binop->getRHS(), BO_LT, binop->getRHS()->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
                BinaryOperator *binop_right = new (context) BinaryOperator(binop->getLHS(), binop->getRHS(), BO_GT, binop->getRHS()->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
                left_expr = DealwithCond(binop_left, logic, cur);
                right_expr = DealwithCond(binop_right, logic, cur);
                return ConnectDNF(left_expr, right_expr);
            }
        }
        else if (binop->getOpcode() == BO_EQ)
        {
            if (!logic)
            {
                BinaryOperator *binop_left = new (context) BinaryOperator(binop->getLHS(), binop->getRHS(), BO_LT, binop->getRHS()->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
                BinaryOperator *binop_right = new (context) BinaryOperator(binop->getLHS(), binop->getRHS(), BO_GT, binop->getRHS()->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
                left_expr = DealwithCond(binop_left, !logic, cur);
                right_expr = DealwithCond(binop_right, !logic, cur);
                return ConnectDNF(left_expr, right_expr);
            }
        }
    }
    if (UnaryOperator *unop = dyn_cast<UnaryOperator>(condition))
    {
        if (unop->getOpcode() == UO_LNot)
        {
            return DealwithCond(unop->getSubExpr(), !logic, cur);
        }
    }
    if (DeclRefExpr *decl = dyn_cast<DeclRefExpr>(condition))
    {
        return DealwithCond(createBinOp(decl, createIntegerLiteral(0), BO_NE), logic, cur);
    }
    if (ParenExpr *paren = dyn_cast<ParenExpr>(condition))
    {
        return DealwithCond(paren->getSubExpr(), logic, cur);
    }
    if (IntegerLiteral *integer = dyn_cast<IntegerLiteral>(condition))
    {
        Expr *Cond = createBinOp(integer, createIntegerLiteral(0), BO_NE);
        return DealwithCond(Cond, logic, cur);
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
            BinaryOperator *binop = dyn_cast<BinaryOperator>(condition);
            Expr *new_binop;
            switch (binop->getOpcode())
            {
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
                LOGWARN("Unexpected Opcode Type: " + string(binop->getOpcodeStr()));
                exit(-1);
            }
            rec_expr.push_back(new_binop);
        }
        else
        {
            outs() << "\n[Deal Contidion Warning] Unexpected type when invert the logic of Expression: " << PrintExpr(condition) << "\n";
            return cur;
        }
    }
    cur.push_back(rec_expr);
    return cur;
}

Expr *ReplaceExprForVar(Expr *expr, string origin_name, string new_name)
{
    if (!expr)
    {
        LOGWARN("Unexpected EmptyExpr in ReplaceExprForVar Function");
        exit(-1);
    }
    if (isa<BinaryOperator>(expr))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
        binop = createBinOp(ReplaceExprForVar(binop->getLHS(), origin_name, new_name), ReplaceExprForVar(binop->getRHS(), origin_name, new_name), binop->getOpcode());
        return binop;
    }
    else if (isa<DeclRefExpr>(expr))
    {
        DeclRefExpr *declRef = dyn_cast<DeclRefExpr>(expr);
        string name = declRef->getDecl()->getNameAsString();
        if (name.find('[') != name.npos)
        {
            regex pattern("(\\w+)\\[(\\w+)\\]");
            smatch matches;
            string::const_iterator searchStart(name.cbegin());
            if (regex_search(searchStart, name.cend(), matches, pattern))
            {
                string match = matches[2].str();
                if (match == origin_name)
                {
                    // 用new_name替换origin_name
                    string old_subscript = matches[1].str() + "[" + origin_name + "]";
                    string new_subscript = matches[1].str() + "[" + new_name + "]";
                    size_t pos = name.find(old_subscript);
                    if (name.find(old_subscript) != string::npos)
                    {
                        name.replace(pos, old_subscript.size(), new_subscript);
                    }
                }
                searchStart = matches.suffix().first;
            }
            declRef = createDeclRefExpr(name);
        }
        else if (name == origin_name)
            declRef = createDeclRefExpr(new_name);
        return declRef;
    }
    else if (isa<ImplicitCastExpr>(expr))
    {
        ImplicitCastExpr *implict = dyn_cast<ImplicitCastExpr>(expr);
        return ReplaceExprForVar(implict->getSubExpr(), origin_name, new_name);
    }
    else if (isa<UnaryOperator>(expr))
    {
        UnaryOperator *unop = dyn_cast<UnaryOperator>(expr);
        return ReplaceExprForVar(unop->getSubExpr(), origin_name, new_name);
    }
    else if (isa<IntegerLiteral>(expr))
    {
    }
    else
    {
        LOGINFO("unexpected type in replacement: " + string(expr->getStmtClassName()));
    }
    return expr;
}
Expr *TransitionSystem::TransExprbyCurVars(Expr *expr, vector<VariableInfo> &Vars)
{
    if (!expr)
    {
        LOGWARN("expr is empty");
        exit(-1);
    }
    if (isa<BinaryOperator>(expr))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
        binop = createBinOp(TransExprbyCurVars(binop->getLHS(), Vars), TransExprbyCurVars(binop->getRHS(), Vars), binop->getOpcode());
        return binop;
    }
    else if (isa<DeclRefExpr>(expr))
    {
        DeclRefExpr *declRef = dyn_cast<DeclRefExpr>(expr);
        string name = declRef->getDecl()->getNameAsString();
        VariableInfo var;
        QualType emptyType;
        var.assign(name, declRef, emptyType);
        return VariableInfo::search_for_value(var, Vars);
    }
    else if (isa<ImplicitCastExpr>(expr))
    {
        ImplicitCastExpr *implict = dyn_cast<ImplicitCastExpr>(expr);
        return TransExprbyCurVars(implict->getSubExpr(), Vars);
    }
    else if (isa<IntegerLiteral>(expr))
    {
    }
    else
    {
        outs() << "[Info] Unexpected Type in Function TransExprbyCurVars : " << expr->getStmtClassName() << "\n"
               << PrintExpr(expr) << '\n';
    }
    return expr;
}

void TransitionSystem::EliminatePath(var_info *total_info)
{
    LOGINFO("Before Eliminate impossible path");
    PrintDNF();
    for (int i = 0; i < DNF.size(); i++)
    {
        C_Polyhedron *p = new C_Polyhedron(total_info->getDim() * 2, UNIVERSE);
        for (int j = 0; j < DNF[i].size(); j++)
        {
            if (CheckBreakFlag(DNF[i][j]))
                continue;
            p->add_constraints(*TransExprtoConstraints(DNF[i][j], TransformationType::Trans, total_info));
        }
        for (int j = 0; j < InequalityDNF[i].size(); j++)
        {
            p->add_constraints(*TransExprtoConstraints(InequalityDNF[i][j], TransformationType::Loc, total_info));
        }
        if (p->is_empty())
        {
            DNF.erase(DNF.begin() + i);
            InequalityDNF.erase(InequalityDNF.begin() + i);
            i--;
        }
    }
    return;
}

void TransitionSystem::InitializeLocTrans(int locsize, Expr *condition, var_info *total_info)
{
    vector<vector<Constraint_System *>> guard;
    vector<vector<Constraint_System *>> guard_primed;
    unordered_set<int> break_branch;
    for (int i = 0; i < DNF.size(); i++)
    {
        for (int j = 0; j < DNF[i].size(); j++)
        {
            if (CheckBreakFlag(DNF[i][j]))
            {
                break_branch.insert(i);
                break;
            }
        }
    }
    guard.resize(InequalityDNF.size());
    guard_primed.resize(InequalityDNF.size());
    for (int i = 0; i < InequalityDNF.size(); i++)
    {
        for (int j = 0; j < InequalityDNF[i].size(); j++)
        {
            guard_primed[i].push_back(TransExprtoConstraints(InequalityDNF[i][j], TransformationType::Guard, total_info));
            guard[i].push_back(TransExprtoConstraints(InequalityDNF[i][j], TransformationType::Loc, total_info));
        }
    }
    for (int i = 0; i < locsize; i++)
    {
        string locname = "Location_" + to_string(i);
        if (i == locsize - 1)
            locname = "le";
        Location *loc = new Location(info->getDim(), info, dualInfo, lambdaInfo, locname);
        loclist->push_back(loc);
    }
    for (int i = 0; i < total_info->getDim(); i++)
    {
        string name = total_info->get_name(i);
        for (auto function_name : MainFuncs)
        {
            if (name.find(function_name) != name.npos)
            {
                project_set.insert(Variable(i + total_info->getDim()));
            }
        }
    }

    for (int i = 0; i < locsize; i++)
    {
        if (i == locsize - 1)
            continue;
        for (int j = 0; j < locsize; j++)
        {
            string trans_name;
            C_Polyhedron *p;
            p = new C_Polyhedron(total_info->getDim() * 2, UNIVERSE);
            for (int index = 0; index < DNF[i].size(); index++)
                if (!CheckBreakFlag(DNF[i][index]))
                    p->add_constraints(*TransExprtoConstraints(DNF[i][index], TransformationType::Trans, total_info));
            for (int index = 0; index < guard[i].size(); index++)
                p->add_constraints(*guard[i][index]);
            if (break_branch.find(i) != break_branch.end())
            {
                if (j != locsize - 1)
                    continue;
                trans_name = "Exit_Transition_from_" + to_string(i) + "by breakstmt";
                p->remove_space_dimensions(project_set);
                TransitionRelation *trans = new TransitionRelation(info->getDim(), info, dualInfo, lambdaInfo, trans_name);
                trans->set_locs((*loclist)[i], (*loclist)[j]);
                trans->set_relation(p);
                trlist->push_back(trans);
                continue;
            }
            if (j != locsize - 1)
            {
                for (int index = 0; index < guard_primed[j].size(); index++)
                    p->add_constraints(*guard_primed[j][index]);
                if (p->is_empty())
                    continue;
                trans_name = "Transition_" + to_string(i) + "_" + to_string(j);
                p->remove_space_dimensions(project_set);
                TransitionRelation *trans = new TransitionRelation(info->getDim(), info, dualInfo, lambdaInfo, trans_name);
                trans->set_locs((*loclist)[i], (*loclist)[j]);
                trans->set_relation(p);
                trlist->push_back(trans);
            }
            else
            {
                C_Polyhedron *q = new C_Polyhedron(total_info->getDim() * 2, UNIVERSE);
                Expr *notExpr = NegateExpr(condition);
                vector<vector<Expr *>> notcond;
                vector<vector<Constraint_System *>> exit_guard;
                notcond = DealwithCond(notExpr, true, notcond);
                exit_guard.resize(notcond.size());
                for (int k = 0; k < notcond.size(); k++)
                    for (int index = 0; index < notcond[k].size(); index++)
                        exit_guard[k].push_back(TransExprtoConstraints(notcond[k][index], TransformationType::Guard, total_info));
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
                    q->remove_space_dimensions(project_set);
                    TransitionRelation *trans = new TransitionRelation(info->getDim(), info, dualInfo, lambdaInfo, trans_name);
                    trans->set_locs((*loclist)[i], (*loclist)[j]);
                    trans->set_relation(q);
                    trlist->push_back(trans);
                }
            }
        }
    }
    return;
}

void TransitionSystem::ComputeInv(Expr *condition, unordered_set<string> vars_in_dnf, vector<C_Polyhedron> init_polys, var_info *total_info)
{
    // DONE: delete the unused variables in InitDNF.
    // DONE: Transform every path into a transition from one path to another.
    // DONE: Construct Location and Transition, and get the InequalityDNF , then print.
    // DONE: add variable_init to info.
    // DONE: alter the mode of the TransExprtoConstraints
    if (comments.size() == 0)
    {
        LOGWARN("No Comments has been added to the transystem.");
        exit(-1);
    }
    ACSLComment *LoopComment = getCurComment();
    EliminatePath(total_info);
    int locsize = DNF.size() + 1;
    vector<vector<Expr *>> invariant;
    LOGINFO(to_string(init_polys.size()));
    for (int i = 0; i < init_polys.size(); i++)
    {
        for (int j = 0; j < locsize; j++)
        {
            // TODO: Clarify that what should be clear and how to save the transition information to save time.
            // TODO: Further optimize the implementation of processing poly.
            // DONE: remove useless result.
            if (j == locsize - 1)
                continue;
            loclist = new vector<Location *>();
            trlist = new vector<TransitionRelation *>();
            InitializeLocTrans(locsize, condition, total_info);
            (*loclist)[j]->setInitPoly(init_polys[i]);
            Print_Location_and_Transition();
            Compute_Invariant_Frontend();
            vector<C_Polyhedron> LoopInv = (*loclist)[locsize - 1]->get_vp_inv().get_vp();
            invariant = ConnectDNF(invariant, TransPolystoExprs(LoopInv, true));
            // PrintDNF(TransPolystoExprs(LoopInv));
            LoopComment->add_invariant(TransPolystoExprs(LoopInv, true), true);
            LoopInv.clear();

            for (int index = 0; index < locsize - 1; index++)
            {
                LoopInv.push_back((*loclist)[index]->GetInv());
            }
            // PrintDNF(TransPolystoExprs(LoopInv));
            LoopComment->add_invariant(TransPolystoExprs(LoopInv, true), true);
            delete loclist, trlist;
        }
    }
    InequalityDNF = invariant;
    LoopComment->AddAssignVars(vars_in_dnf);
    return;
}

vector<vector<Expr *>> TransitionSystem::OutLoop(Expr *cond, unordered_set<string> &UsedVars, vector<vector<Expr *>> &InitDNF, vector<vector<Expr *>> &InitIneqDNF, vector<vector<VariableInfo>> &InitVars, unordered_set<string> &LocalVars)
{
    if (info && dualInfo && lambdaInfo)
    {
        delete info, dualInfo, lambdaInfo;
        info = NULL;
        dualInfo = NULL;
        lambdaInfo = NULL;
    }
    info = new var_info();
    lambdaInfo = new var_info();
    dualInfo = new var_info();
    var_info *total_info = new var_info();
    LOGINFO("Collect Loop Transition Relation");
    PrintDNF();
    for (int i = 0; i < InitDNF.size(); i++)
    {
        for (int j = 0; j < InitDNF[i].size(); j++)
        {
            if (TraverseExprCheckVar(InitDNF[i][j], UsedVars))
            {
                TraverseExprForVars(InitDNF[i][j], UsedVars);
            }
        }
    }
    for (int i = 0; i < InitIneqDNF.size(); i++)
    {
        for (int j = 0; j < InitIneqDNF[i].size(); j++)
        {
            if (TraverseExprCheckVar(InitIneqDNF[i][j], UsedVars))
            {
                TraverseExprForVars(InitIneqDNF[i][j], UsedVars);
            }
        }
    }
    unordered_set<string> rec_vars = UsedVars;
    UsedVars.clear();
    for (const auto &var : rec_vars)
    {
        total_info->search_and_insert(var.c_str());
    }
    for (const auto &var : rec_vars)
    {
        total_info->search_and_insert((var + INITSUFFIX).c_str());
    }
    for (const auto &var : LocalVars)
    {
        total_info->search_and_insert(var.c_str());
    }
    for (const auto &var : LocalVars)
    {
        total_info->search_and_insert((var + INITSUFFIX).c_str());
    }
    for (int i = 0; i < total_info->getDim(); i++)
    {
        string name = total_info->get_name(i);
        bool flag = false;
        for (auto function_name : MainFuncs)
        {
            if (name.find(function_name) != name.npos)
            {
                project_set.insert(Variable(i));
                flag = true;
            }
        }
        if (!flag)
        {
            info->insert(name.c_str());
            if (name.find(INITSUFFIX) == name.npos)
                UsedVars.insert(name);
        }
    }
    vector<C_Polyhedron> init_polys = ComputeInitPolys(rec_vars, cond, InitDNF, InitIneqDNF, InitVars, total_info);
    for (int i = 0; i < init_polys.size(); i++)
        init_polys[i].remove_space_dimensions(project_set);
    ACSLComment *comment = getCurComment();
    // DONE: add the remaining DNF into the comment.
    vector<vector<Expr *>> RemainDNF = AppendDNF(InitDNF, InitIneqDNF);
    bool flag = false;
    // vector<C_Polyhedron *> polys;
    // var_info* rec_info=new var_info;
    // for(int i=0;i<total_info->getDim();i++)
    //     rec_info->insert(total_info->get_name(i));
    // Variables_Set rec_project;
    // for(int i=0;i<RemainDNF.size();i++){
    //     for(int j=0;j<RemainDNF[i].size();j++){
    //         unordered_set<string> rec;
    //         TraverseExprForVars(RemainDNF[i][j],rec);
    //         for(auto name:rec){
    //             rec_info->search_and_insert(name.c_str());
    //         }
    //     }
    // }

    // for(int i=0;i<rec_info->getDim();i++){
    //     string name=rec_info->get_name(i);
    //     if (name.find(INITSUFFIX)!=name.npos)
    //         rec_project.insert(Variable(i));
    // }
    // LOGINFO("here");
    // PrintDNF(RemainDNF);
    for (int i = 0; i < RemainDNF.size(); i++)
    {
        if (RemainDNF[i].size() != 0)
            flag = true;
        else
            continue;
        // C_Polyhedron *p = new C_Polyhedron(rec_info->getDim(), UNIVERSE);
        // for (int j = 0; j < RemainDNF[i].size(); j++)
        // {
        //     p->add_constraints(*TransExprtoConstraints(RemainDNF[i][j], TransformationType::Loc, rec_info));
        // }
        // p->remove_space_dimensions(rec_project);
        // if (p->is_universe())
        // {
        //     RemainDNF.erase(RemainDNF.begin() + i);
        //     i--;
        // }
        // if (!p->is_empty())
        //     polys.push_back(p);
    }
    // RemainDNF = TransPolystoExprs(polys, true);
    // LOGINFO("note here");
    // PrintDNF(RemainDNF);
    AddFundExpr(rec_vars);
    ComputeInv(cond, UsedVars, init_polys, total_info);

    InWhileLoop = false;
    Vars.clear();
    DNF.clear();
    project_set.clear();
    Verified_Loop_Count++;
    if (!flag)
        RemainDNF.clear();
    delete total_info;
    return RemainDNF;
}

void TransitionSystem::AfterLoop(vector<vector<Expr *>> &dnf, unordered_set<string> &UsedVars)
{
    for (int i = 0; i < dnf.size(); i++)
    {
        for (int j = 0; j < dnf[i].size(); j++)
        {
            if (!TraverseExprCheckVars(dnf[i][j], UsedVars))
            {
                dnf[i].erase(dnf[i].begin() + j);
                j--;
            }
        }
    }
    InequalityDNF = ConnectDNF(InequalityDNF, dnf);
    DNF.resize(InequalityDNF.size());
    Vars.resize(InequalityDNF.size());
    return;
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
void TransitionSystem::ProcessSkipDNF(vector<vector<Expr *>> &dnf)
{
    for (int i = 0; i < dnf.size(); i++)
    {
        for (int j = 0; j < dnf[i].size(); j++)
        {
            eliminate_initsuffix(dnf[i][j]);
            if (isa<BinaryOperator>(dnf[i][j]))
            {
                BinaryOperator *binop = dyn_cast<BinaryOperator>(dnf[i][j]);
                if (binop->getOpcode() == BO_Assign)
                    binop->setOpcode(BO_EQ);
            }
        }
    }
    deduplicate(dnf);
    return;
}

// unordered_set<string> DFS_VarGraph(int cur, unordered_set<string> &visited, vector<string> &node, map<string, int> &cor_index, VarGraph *graph)
// {
//     unordered_set<string> possibles;
//     string cur_name = node[cur];
//     visited.insert(cur_name);
//     possibles.insert(cur_name);
//     unordered_set<string> to = graph->edges[cur_name];
//     for (const auto &to_name : to)
//     {
//         if (visited.find(to_name) != visited.end())
//         {
//             unordered_set<string> traverse_var = graph->possible_rv[to_name];
//             possibles.insert(traverse_var.begin(), traverse_var.end());
//             continue;
//         }
//         if (cor_index.find(to_name) == cor_index.end())
//         {
//             possibles.insert(to_name);
//             continue;
//         }
//         unordered_set<string> traverse_var = DFS_VarGraph(cor_index[to_name], visited, node, cor_index, graph);
//         possibles.insert(traverse_var.begin(), traverse_var.end());
//     }
//     graph->possible_rv[cur_name] = possibles;
//     return possibles;
// }

// void TransitionSystem::Construct_Graph()
// {
//     for (int i = 0; i < Vars.size(); i++)
//     {
//         VarGraph graph;
//         for (int j = 0; j < Vars[i].size(); j++)
//         {
//             unordered_set<string> UsedVars;
//             Expr *expr = Vars[i][j].getVarValue();
//             string var_name = Vars[i][j].getVarName();
//             TraverseExprForVars(expr, UsedVars);
//             graph.edges[var_name] = UsedVars;
//         }
//         Graphs.push_back(graph);
//     }
//     for (int i = 0; i < Graphs.size(); i++)
//     {
//         VarGraph *graph = &Graphs[i];
//         vector<string> node;
//         unordered_set<string> visited;
//         map<string, int> cor_index;
//         visited.clear();
//         for (auto &pair : graph->edges)
//             node.push_back(pair.first);
//         for (int j = 0; j < node.size(); j++)
//         {
//             cor_index[node[j]] = j;
//         }
//         for (int j = 0; j < node.size(); j++)
//         {
//             if (visited.find(node[j]) == visited.end())
//                 DFS_VarGraph(j, visited, node, cor_index, graph);
//         }
//     }
//     return;
// }

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
    : Verified_Loop_Count(0),
      Vars(other.Vars),
      DNF(other.DNF),
      InequalityDNF(other.InequalityDNF)
//   InWhileLoop(other.InWhileLoop),
//   Inner_Loop_Depth(other.Inner_Loop_Depth),
//   Inner_Loop_Count(other.Inner_Loop_Count)
{
}

void TransitionSystem::InitCanonical(int size)
{
    Vars.clear();
    DNF.clear();
    Vars.resize(size);
    DNF.resize(size);
    return;
}

void TransitionSystem::PrintVars()
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
            outs() << "\t Variable Name is:" << Vars[i][j].getVarName() << '\n';
            outs() << "\t Variable Value is:";
            if (Vars[i][j].getVarValue())
            {
                outs() << PrintExpr(Vars[i][j].getVarValue()) << "\n";
            }
            else
            {
                outs() << "No Initialized." << '\n';
            }
            outs() << "\t Variable Type is: " << Vars[i][j].getQualType().getAsString() << '\n';
        }
    }
}
void TransitionSystem::PrintDNF()
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
            raw_string_ostream rso(str);
            DNF[i][j]->printPretty(rso, nullptr, Policy);
            rso.flush();
            outs() << str << "\n";
        }
        outs() << "DNF disjunctive clause " << i << " is printed.\n";
    }
    outs() << "\n";
    outs() << "[Print InequalityDNF Information]\n";
    for (int i = 0; i < InequalityDNF.size(); i++)
    {
        outs() << "InequalityDNF disjunctive branch " << i << " and its size is:" << InequalityDNF[i].size() << '\n';
        for (int j = 0; j < InequalityDNF[i].size(); j++)
        {
            outs() << "\t[InequalityDNF Number " << j << " is:]"
                   << "\n";
            outs() << "\t";

            outs() << PrintExpr(InequalityDNF[i][j]) << "\n";
        }
        outs() << "InequalityDNF disjunctive clause " << i << " is printed.\n";
    }
    return;
}

bool TransitionSystem::CheckArrayExist()
{
    for (int i = 0; i < Vars.size(); i++)
    {
        for (int j = 0; j < Vars[i].size(); j++)
        {
            VariableInfo var = Vars[i][j];
            string VarName = var.getVarName();
            if (VarName.find('[') != VarName.npos)
                return true;
            Expr *VarValue = var.getVarValue();
            unordered_set<string> UsedVars;
            TraverseExprForVars(VarValue, UsedVars);
            for (auto RecVarName : UsedVars)
            {
                if (RecVarName.find('[') != RecVarName.npos)
                    return true;
            }
        }
    }
    for (int i = 0; i < InequalityDNF.size(); i++)
    {
        for (int j = 0; j < InequalityDNF[i].size(); j++)
        {
            Expr *RecExpr = InequalityDNF[i][j];
            unordered_set<string> UsedVars;
            TraverseExprForVars(RecExpr, UsedVars);
            for (auto RecVarName : UsedVars)
            {
                if (RecVarName.find('[') != RecVarName.npos)
                    return true;
            }
        }
    }
    return false;
}

bool TransitionSystem::CheckArrayIncr(ArrIndex RecArrIndex)
{
    if (ArrayIndex.size() == 0)
        return false;
    string IndexName = RecArrIndex.IndexName;
    for (int i = 0; i < Vars.size(); i++)
    {
        for (int j = 0; j < Vars[i].size(); j++)
        {
            VariableInfo var = Vars[i][j];
            string VarName = var.getVarName();
            if (VarName != IndexName)
                continue;
            Expr *VarValue = var.getVarValue();
            // Check Whether it's index=index+1 or index++;
            if (!isa<BinaryOperator>(VarValue))
            {
                LOGWARN("Infeasible Index Incr: " + PrintExpr(VarValue));
                exit(-1);
            }
            BinaryOperator *binop = dyn_cast<BinaryOperator>(VarValue);
            if (binop->getOpcode() != BO_Add)
            {
                LOGWARN("Infeasible Index Incr: " + PrintExpr(VarValue));
                exit(-1);
            }
            int flag = 0;
            Expr *left = binop->getLHS();
            Expr *right = binop->getRHS();
            if (isa<ImplicitCastExpr>(left))
                left = (dyn_cast<ImplicitCastExpr>(left))->getSubExpr();
            if (isa<ImplicitCastExpr>(right))
                right = (dyn_cast<ImplicitCastExpr>(right))->getSubExpr();
            if (isa<DeclRefExpr>(left))
            {
                DeclRefExpr *DeclLeft = dyn_cast<DeclRefExpr>(left);
                if (DeclLeft->getDecl()->getNameAsString() != IndexName)
                {
                    LOGWARN("Infeasible Index Incr: " + PrintExpr(VarValue));
                    exit(-1);
                }
                if (flag == 0)
                    flag = 1;
                else if (flag == 2)
                    flag = 3;
                else
                {
                    LOGWARN("Infeasible Index Incr: " + PrintExpr(VarValue));
                    exit(-1);
                }
            }
            else if (isa<IntegerLiteral>(left))
            {
                IntegerLiteral *IntegerLeft = dyn_cast<IntegerLiteral>(left);
                if (IntegerLeft->getValue() != 1)
                {
                    LOGWARN("Infeasible Index Incr: " + PrintExpr(VarValue));
                    exit(-1);
                }
                if (flag == 0)
                    flag = 2;
                else if (flag == 1)
                    flag = 3;
                else
                {
                    LOGWARN("Infeasible Index Incr: " + PrintExpr(VarValue));
                    exit(-1);
                }
            }
            else
            {
                LOGWARN("Infeasible Index Incr: " + PrintExpr(VarValue));
                exit(-1);
            }
            if (isa<DeclRefExpr>(right))
            {
                DeclRefExpr *DeclRight = dyn_cast<DeclRefExpr>(right);
                if (DeclRight->getDecl()->getNameAsString() != IndexName)
                {
                    LOGWARN("Infeasible Index Incr: " + PrintExpr(VarValue));
                    exit(-1);
                }
                if (flag == 0)
                    flag = 1;
                else if (flag == 2)
                    flag = 3;
                else
                {
                    LOGWARN("Infeasible Index Incr: " + PrintExpr(VarValue));
                    exit(-1);
                }
            }
            else if (isa<IntegerLiteral>(right))
            {
                IntegerLiteral *IntegerRight = dyn_cast<IntegerLiteral>(right);
                if (IntegerRight->getValue() != 1)
                {
                    LOGWARN("Infeasible Index Incr: " + PrintExpr(VarValue));
                    exit(-1);
                }
                if (flag == 0)
                    flag = 2;
                else if (flag == 1)
                    flag = 3;
                else
                {
                    LOGWARN("Infeasible Index Incr: " + PrintExpr(VarValue));
                    exit(-1);
                }
            }
            else
            {
                LOGWARN("Infeasible Index Incr: " + PrintExpr(VarValue));
                exit(-1);
            }
            if (flag != 3)
            {
                LOGWARN("Infeasible Index Incr: " + PrintExpr(VarValue));
                exit(-1);
            }
        }
    }
    return true;
}

bool TransitionSystem::CheckModeOne()
{
    int VarSize = Vars.size();
    int DNFSize = DNF.size();
    int IneqDNFSize = InequalityDNF.size();
    if (VarSize == DNFSize && DNFSize == IneqDNFSize && IneqDNFSize == 1)
        return true;
    else
        return false;
}

bool TransitionSystem::CheckModeTwo(string &FlagVar)
{
    unordered_set<string> CheckedVars;
    for (int i = 0; i < Vars.size(); i++)
    {
        for (int j = 0; j < Vars[i].size(); j++)
        {
            VariableInfo var = Vars[i][j];
            string VarName = var.getVarName();
            if (VarName.find('[') != VarName.npos)
                continue;
            if (CheckedVars.find(VarName) != CheckedVars.end())
                continue;
            CheckedVars.insert(VarName);
            Expr *VarValue = var.getVarValue();
            if (!VarValue)
                continue;
            if (!VarValue->isConstantInitializer(*context, false))
                continue;
            bool flag = true;
            for (int index = 0; index < Vars.size(); index++)
            {
                for (int subindex = 0; subindex < Vars[index].size(); subindex++)
                {
                    VariableInfo Subvar = Vars[index][subindex];
                    string SubVarName = Subvar.getVarName();
                    if (SubVarName != VarName)
                        continue;
                    Expr *SubVarValue = Subvar.getVarValue();
                    if (!SubVarValue)
                    {
                        flag = false;
                        break;
                    }
                    if (!SubVarValue->isConstantInitializer(*context, false))
                    {
                        flag = false;
                        break;
                    }
                    if (isa<IntegerLiteral>(SubVarValue) && isa<IntegerLiteral>(VarValue))
                    {
                        IntegerLiteral *MainValue = dyn_cast<IntegerLiteral>(VarValue);
                        IntegerLiteral *SubValue = dyn_cast<IntegerLiteral>(SubVarValue);
                        if (MainValue->getValue() != SubValue->getValue())
                        {
                            flag = false;
                            break;
                        }
                    }
                    else
                    {
                        LOGWARN("Unspecified Flag Var Type");
                        exit(-1);
                    }
                }
                if (!flag)
                    break;
            }
            if (flag)
            {
                FlagVar = VarName;
                return true;
            }
        }
    }
    return false;
}

bool TransitionSystem::CheckModeThree()
{
    return false;
}

void TransitionSystem::ArrayInvariantProcess()
{
    if (!CheckArrayExist())
        return;
    for (int i = 0; i < ArrayIndex.size(); i++)
    {
        if (!CheckArrayIncr(ArrayIndex[i]))
            return;
        if (CheckModeOne())
        {
            ArrayInvariantProcessModeOne(ArrayIndex[i]);
            return;
        }
        string FlagVar;
        if (CheckModeTwo(FlagVar))
            ArrayInvariantProcessModeTwo(FlagVar, ArrayIndex[i]);
        else if (CheckModeThree())
            ArrayInvariantProcessModeThree();
        else
        {
            LOGWARN("Invalid mode specified.");
            exit(-1);
        }
    }

    return;
}

void TransitionSystem::ArrayInvariantProcessModeOne(ArrIndex RecArrIndex)
{
    ACSLComment *RecComment = getCurComment();
    comments.pop_back();
    int LineNum = RecComment->getLineNum();
    ACSLComment *NewComment = new ACSLComment(LineNum, ACSLComment::CommentType::MODEONEINV);
    for (int i = 0; i < Vars.size(); i++)
    {
        for (int j = 0; j < Vars[i].size(); j++)
        {
            VariableInfo var = Vars[i][j];
            string VarName = var.getVarName();
            if (VarName.find("[") == VarName.npos)
                continue;
            regex pattern("(\\w+)\\[(\\w+)\\]");
            smatch matches;
            string::const_iterator searchStart(VarName.cbegin());
            if (regex_search(searchStart, VarName.cend(), matches, pattern))
            {
                if (matches.size() < 3)
                {
                    LOGWARN("Unexpected pattern");
                    exit(-1);
                }
                string match = matches[2].str();
                if (match != RecArrIndex.IndexName)
                    continue;
            }
            Expr *VarValue = var.getVarValue();
            NewComment->AddArrayInv(createBinOp(createDeclRefExpr(VarName), VarValue, BO_EQ), RecArrIndex);
            Vars[i].erase(Vars[i].begin() + j);
            j--;
        }
    }
    AddComment(NewComment);
    AddComment(RecComment);
    EliminateArray();
    return;
}

void TransitionSystem::ArrayInvariantProcessModeTwo(string FlagVar, ArrIndex RecArrIndex)
{
    ACSLComment *RecComment = getCurComment();
    comments.pop_back();
    int LineNum = RecComment->getLineNum();
    ACSLComment *ExistComment = new ACSLComment(LineNum, ACSLComment::CommentType::MODETWOEXISTINV);
    ACSLComment *ForallComment = new ACSLComment(LineNum, ACSLComment::CommentType::MODETWOALLINV);
    Expr *ExistInv = NULL;
    Expr *ForallInv = NULL;
    Expr *RecFlagExpr = NULL;
    LOGINFO(FlagVar);
    for (int i = 0; i < Vars.size(); i++)
    {
        bool BranchFlag = false;
        for (int j = 0; j < Vars[i].size(); j++)
        {
            VariableInfo var = Vars[i][j];
            string VarName = var.getVarName();
            if (VarName != FlagVar)
                continue;
            else
                BranchFlag = true;
            Expr *expr = var.getVarValue();
            RecFlagExpr = expr;
            for (int index = 0; index < InequalityDNF[i].size(); index++)
            {
                Expr *cond = InequalityDNF[i][index];
                unordered_set<string> RecVars;
                TraverseExprForVars(cond, RecVars);
                for (auto name : RecVars)
                {
                    if (name.find('[') == name.npos)
                        continue;
                    regex pattern("(\\w+)\\[(\\w+)\\]");
                    smatch matches;
                    string::const_iterator searchStart(name.cbegin());
                    if (regex_search(searchStart, name.cend(), matches, pattern))
                    {
                        if (matches.size() < 3)
                        {
                            LOGWARN("Unexpected pattern");
                            exit(-1);
                        }
                        string match = matches[2].str();
                        if (match != RecArrIndex.IndexName)
                            break;
                    }
                    if (ExistInv)
                    {
                        ExistInv = createBinOp(ExistInv, cond, BO_LOr);
                        ForallInv = createBinOp(ForallInv, cond, BO_LAnd);
                    }
                    else
                    {
                        ExistInv = cond;
                        ForallInv = cond;
                    }
                    break;
                }
            }
        }
    }
    ExistComment->AddFlagExpr(createBinOp(createDeclRefExpr(FlagVar), RecFlagExpr, BO_EQ));
    ForallComment->AddFlagExpr(createBinOp(createDeclRefExpr(FlagVar), RecFlagExpr, BO_NE));
    ExistComment->AddArrayInv(ExistInv,RecArrIndex);
    ForallComment->AddArrayInv(ForallInv,RecArrIndex);
    AddComment(ExistComment);
    AddComment(ForallComment);
    AddComment(RecComment);
    EliminateArray();
    return;
}

void TransitionSystem::ArrayInvariantProcessModeThree()
{
}

void TransitionSystem::EliminateArray()
{
    for (int i = 0; i < Vars.size(); i++)
    {
        for (int j = 0; j < Vars[i].size(); j++)
        {
            VariableInfo var = Vars[i][j];
            Expr *VarValue = var.getVarValue();
            unordered_set<string> UsedVars;
            TraverseExprForVars(VarValue, UsedVars);
            for (auto RecName : UsedVars)
            {
                if (RecName.find('[') != RecName.npos)
                {
                    Vars[i].erase(Vars[i].begin() + j);
                    j--;
                    break;
                }
            }
        }
    }
    for (int i = 0; i < InequalityDNF.size(); i++)
    {
        for (int j = 0; j < InequalityDNF[i].size(); j++)
        {
            Expr *expr = InequalityDNF[i][j];
            unordered_set<string> UsedVars;
            TraverseExprForVars(expr, UsedVars);
            for (auto RecName : UsedVars)
            {
                if (RecName.find('[') != RecName.npos)
                {
                    InequalityDNF[i].erase(InequalityDNF[i].begin() + j);
                    j--;
                    break;
                }
            }
        }
    }
}
void TransitionSystem::init()
{
    InequalityDNF.resize(1);
    DNF.resize(1);
    Vars.resize(1);
    ArrayIndex.clear();
    Verified_Loop_Count = 0;
    return;
}

void TransitionSystem::clear()
{
    DNF.clear();
    InequalityDNF.clear();
    Vars.clear();
    return;
}