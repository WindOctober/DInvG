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
extern unordered_set<string> global_vars;
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
void TransitionSystem::Print_DNF(vector<vector<Expr *>> DNF)
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

void Print_DNF(vector<vector<Expr *>> &DNF)
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

string Print_Expr(Expr *expr)
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
                // outs() << "\n[check_guard info] The Expr " << Print_Expr(expr) << " is guard";
                return true;
            }
            else
            {
                // outs() << "\n[check_guard info] The Expr " << Print_Expr(expr) << " is not guard";
                return false;
            }
        }
        else
        {
            // outs() << "\n[check_guard info] The Expr " << Print_Expr(expr) << " is not guard";
            return false;
        }
    }
    else
    {
        // outs() << "\n[check_guard warning] The Unexpected Expr type " << Print_Expr(expr) << "";
        return false;
    }
}

Expr *Trans_LinExpr_to_Expr(Linear_Expression *lin_expr, string eliminate_var)
{
    Expr *res = NULL;
    for (int i = 0; i < info->get_dimension(); i++)
    {
        string var_name = info->get_name(i);
        Expr *rec_expr;
        if (var_name == eliminate_var)
            continue;
        int coef = lin_expr->coefficient(Variable(i)).get_si();
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

Linear_Expression *Trans_Expr_to_LinExpr(Expr *expr, enum TransformationType type, int var_size)
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

Expr *Trans_Constraint_to_Expr(Constraint constraint)
{
    // NOTE: Constraint should not contain initial variables
    ASTContext *Context = TransitionSystem::context;
    // Create an Expr for the linear expression part of the constraint.
    Expr *res = nullptr;
    auto lin_expr = constraint.expression();
    FPOptions default_options;
    for (int i = 0; i < info->get_dimension(); i++)
    {
        string name = info->get_name(i);
        int coef = lin_expr.coefficient(Variable(i)).get_si();
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

    Coefficient coef = lin_expr.inhomogeneous_term();
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

Constraint_System *Trans_Expr_to_Constraints(Expr *expr, enum TransformationType type, int var_size)
{
    // DONE: confirm the expr template, which must be xxx <=/==/>= xxx;
    Constraint_System *constraint = new Constraint_System();
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
                var.alterVar(binop->getLHS(), binop->getRHS());
                int index = info->search(var.getVariableName().c_str());
                if (type == TransformationType::Trans)
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

bool Traverse_Expr_ForVar(Expr *expr, string var_name)
{
    if (!expr)
        return false;
    if (CheckBreakFlag(expr))
        return true;
    bool flag = false;
    if (isa<BinaryOperator>(expr))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
        flag |= Traverse_Expr_ForVar(binop->getLHS(), var_name);
        flag |= Traverse_Expr_ForVar(binop->getRHS(), var_name);
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
        flag |= Traverse_Expr_ForVar(implict->getSubExpr(), var_name);
    }
    else if (isa<IntegerLiteral>(expr))
    {
    }
    else if (isa<UnaryOperator>(expr))
    {
        UnaryOperator *unop = dyn_cast<UnaryOperator>(expr);
        flag |= Traverse_Expr_ForVar(unop->getSubExpr(), var_name);
    }
    else if (isa<ParenExpr>(expr))
    {
        ParenExpr *paren = dyn_cast<ParenExpr>(expr);
        flag |= Traverse_Expr_ForVar(paren->getSubExpr(), var_name);
    }
    else
    {
        LOG_INFO("Unexpected Type in Function Traverse_Expr_ForVars :");
        LOG_INFO(Print_Expr(expr));
        exit(-1);
    }
    return flag;
}

bool Traverse_Expr_CheckVar(Expr *expr, const unordered_set<string> &res)
{
    if (CheckBreakFlag(expr))
        return true;
    bool flag = false;
    if (isa<BinaryOperator>(expr))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
        flag |= Traverse_Expr_CheckVar(binop->getLHS(), res);
        flag |= Traverse_Expr_CheckVar(binop->getRHS(), res);
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
        flag |= Traverse_Expr_CheckVar(implict->getSubExpr(), res);
    }
    else if (isa<IntegerLiteral>(expr))
    {
    }
    else if (isa<UnaryOperator>(expr))
    {
        UnaryOperator *unop = dyn_cast<UnaryOperator>(expr);
        flag |= Traverse_Expr_CheckVar(unop->getSubExpr(), res);
    }
    else if (isa<ParenExpr>(expr))
    {
        ParenExpr *paren = dyn_cast<ParenExpr>(expr);
        flag |= Traverse_Expr_CheckVar(paren->getSubExpr(), res);
    }
    else
    {
        LOG_INFO("Unexpected Type in Function Traverse_Expr_ForVars :");
        LOG_INFO(Print_Expr(expr));
        exit(-1);
    }
    return flag;
}

bool Traverse_Expr_CheckVars(Expr *expr, const unordered_set<string> &res)
{
    if (CheckBreakFlag(expr))
        return true;
    bool flag = true;
    if (isa<BinaryOperator>(expr))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
        flag &= Traverse_Expr_CheckVars(binop->getLHS(), res);
        flag &= Traverse_Expr_CheckVars(binop->getRHS(), res);
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
        flag &= Traverse_Expr_CheckVars(implict->getSubExpr(), res);
    }
    else if (isa<IntegerLiteral>(expr))
    {
    }
    else if (isa<UnaryOperator>(expr))
    {
        UnaryOperator *unop = dyn_cast<UnaryOperator>(expr);
        flag &= Traverse_Expr_CheckVars(unop->getSubExpr(), res);
    }
    else if (isa<ParenExpr>(expr))
    {
        ParenExpr *paren = dyn_cast<ParenExpr>(expr);
        flag &= Traverse_Expr_CheckVars(paren->getSubExpr(), res);
    }
    else
    {
        LOG_INFO("Unexpected Type in Function Traverse_Expr_ForVars :");
        LOG_INFO(Print_Expr(expr));
        exit(-1);
    }
    return flag;
}

void Traverse_Expr_ForVars(Expr *expr, unordered_set<string> &res)
{
    if (!expr)
        return;
    if (CheckBreakFlag(expr))
        return;
    if (isa<BinaryOperator>(expr))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
        Traverse_Expr_ForVars(binop->getLHS(), res);
        Traverse_Expr_ForVars(binop->getRHS(), res);
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
        Traverse_Expr_ForVars(implict->getSubExpr(), res);
    }
    else if (isa<IntegerLiteral>(expr))
    {
        return;
    }
    else if (isa<UnaryOperator>(expr))
    {
        UnaryOperator *unop = dyn_cast<UnaryOperator>(expr);
        Traverse_Expr_ForVars(unop->getSubExpr(), res);
    }
    else if (isa<ParenExpr>(expr))
    {
        ParenExpr *paren = dyn_cast<ParenExpr>(expr);
        Traverse_Expr_ForVars(paren->getSubExpr(), res);
    }
    else if (isa<CallExpr>(expr)){
        CallExpr *call = dyn_cast<CallExpr>(expr);
        for (int index = 0; index < call->getNumArgs(); index++)
        {
            Expr *call_param = call->getArg(index);
            Traverse_Expr_ForVars(call_param,res);
        }
    }
    else
    {
        LOG_WARNING("Unexpected Type " + string(expr->getStmtClassName()));
        LOG_WARNING(Print_Expr(expr));
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
        LOG_WARNING("Unexpected Type" + string(expr->getStmtClassName()));
        LOG_WARNING(Print_Expr(expr));
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
        LOG_WARNING("Unexpected Type" + string(expr->getStmtClassName()));
        LOG_WARNING(Print_Expr(expr));
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
    else if (isa<IntegerLiteral>(expr))
    {
    }
    else
    {
        LOG_WARNING("Unexpected Type" + string(expr->getStmtClassName()));
        LOG_WARNING(Print_Expr(expr));
        exit(-1);
    }
    return expr;
}
vector<C_Polyhedron> Compute_and_Eliminate_Init_Poly(unordered_set<string> &total_vars, Expr *condition, vector<vector<Expr *>> &init_DNF, vector<vector<Expr *>> &init_ineq_DNF, vector<vector<VariableInfo>> &init_vars)
{
    // TODO: deal with the situation that return size=0;
    // DONE: write the transformation from Constraint to Expression.
    // DONE: think the inequality init_value.
    vector<vector<Expr *>> DNF;
    ASTContext *context = TransitionSystem::context;
    DNF.resize(init_DNF.size());
    assert(init_DNF.size() == init_vars.size());

    for (int i = 0; i < init_DNF.size(); i++)
    {
        unordered_set<string> rec_used;
        for (int j = 0; j < init_vars[i].size(); j++)
        {
            string var_name = init_vars[i][j].getVariableName();
            if (Traverse_Expr_ForVar(init_vars[i][j].getVariableValue(), var_name))
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
    for (int i = 0; i < init_DNF.size(); i++)
    {
        for (int j = 0; j < init_DNF[i].size(); j++)
        {
            if (Traverse_Expr_CheckVars(init_DNF[i][j], total_vars))
            {
                if (!isa<BinaryOperator>(init_DNF[i][j]))
                {
                    LOG_WARNING("Unexpected type of init_DNF.");
                    exit(-1);
                }
                DNF[i].push_back(init_DNF[i][j]);
                init_DNF[i].erase(init_DNF[i].begin() + j);
                j--;
            }
        }
    }
    
    vector<vector<Expr *>> ineq_DNF;
    ineq_DNF.resize(init_ineq_DNF.size());
    for (int i = 0; i < init_ineq_DNF.size(); i++)
    {
        for (int j = 0; j < init_ineq_DNF[i].size(); j++)
        {
            if (Traverse_Expr_CheckVars(init_ineq_DNF[i][j], total_vars))
            {
                ineq_DNF[i].push_back(init_ineq_DNF[i][j]);
                init_ineq_DNF[i].erase(init_ineq_DNF[i].begin() + j);
                j--;
            }
        }
    }
    for (int i = 0; i < ineq_DNF.size(); i++)
    {
        for (int j = 0; j < ineq_DNF[i].size(); j++)
        {
            if (CheckBreakFlag(ineq_DNF[i][j]))
                continue;
            if (!CheckInitSuffix(ineq_DNF[i][j]))
                ineq_DNF[i][j] = Add_InitSuffix(ineq_DNF[i][j]);
        }
    }
    DNF = Append_DNF(DNF, ineq_DNF);
    LOG_INFO("Before Transform init_dnf into polyhedron: ");
    Print_DNF(DNF);
    vector<C_Polyhedron> init_polys;
    for (int i = 0; i < DNF.size(); i++)
    {
        C_Polyhedron *p = new C_Polyhedron(info->get_dimension(), UNIVERSE);
        for (int j = 0; j < DNF[i].size(); j++)
        {
            if (CheckBreakFlag(DNF[i][j]))
                continue;
            p->add_constraints(*Trans_Expr_to_Constraints(DNF[i][j], TransformationType::Loc, info->get_dimension()));
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

void TransitionSystem::add_fundamental_expr(unordered_set<string> &used_vars)
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
                    LOG_WARNING("Invalid DNF type: " + string(DNF[i][j]->getStmtClassName()));
                    exit(-1);
                }
                DeclRefExpr *decl = dyn_cast<DeclRefExpr>(binop->getLHS());
                rec_used.insert(decl->getDecl()->getNameAsString());
            }
            else
            {
                LOG_WARNING("Invalid DNF type: " + string(DNF[i][j]->getStmtClassName()));
                exit(-1);
            }
        }
        for (const auto &name : used_vars)
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

void TransitionSystem::add_fundamental_initexpr(unordered_set<string> &used_vars, vector<vector<Expr *>> &dnf)
{
    assert(Vars.size() == dnf.size());
    for (int i = 0; i < Vars.size(); i++)
    {
        unordered_set<string> rec_used;
        for (int j = 0; j < Vars[i].size(); j++)
        {
            string var_name = Vars[i][j].getVariableName();
            if (var_name == "")
                continue;
            if (Traverse_Expr_ForVar(Vars[i][j].getVariableValue(), var_name))
            {
                rec_used.insert(var_name);
            }
        }
        for (auto name : used_vars)
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

unordered_set<string> TransitionSystem::Merge_Function_Call(vector<vector<Expr *>> &function_dnf, CallExpr *callexpr, string new_return_name, unordered_set<string> global_vars)
{
    vector<vector<Expr *>> fDNF;
    vector<vector<Expr *>> fIneqDNF;
    unordered_set<string> non_local_vars;
    unordered_set<string> rec_vars;
    unordered_set<string> local_vars;
    FunctionDecl *func = callexpr->getDirectCallee();
    string return_name = func->getNameAsString() + "_RetVal";
    non_local_vars.insert(new_return_name);
    non_local_vars.insert(global_vars.begin(), global_vars.end());
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
                LOG_WARNING("unexpected type: " + string(subexpr->getStmtClassName()));
            }
            if (unop->getOpcode() == UO_AddrOf)
            {
                string origin_name = "*" + param->getNameAsString();
                non_local_vars.insert(call_name);
                for (int i = 0; i < function_dnf.size(); i++)
                {
                    for (int j = 0; j < function_dnf[i].size(); j++)
                    {
                        function_dnf[i][j] = replace_expr_for_var(function_dnf[i][j], origin_name, call_name);
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
            LOG_INFO("cannot deal with expression in callfunction param");
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
                    function_dnf[i][j] = replace_expr_for_var(function_dnf[i][j], "*" + param->getNameAsString(), "*" + call_name);
                    non_local_vars.insert("*" + call_name);
                }
            }
        }
        else
        {
            for (int i = 0; i < function_dnf.size(); i++)
            {
                for (int j = 0; j < function_dnf[i].size(); j++)
                {
                    function_dnf[i][j] = replace_expr_for_var(function_dnf[i][j], param->getNameAsString(), call_name);
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
            function_dnf[i][j] = replace_expr_for_var(function_dnf[i][j], return_name, new_return_name);

            Traverse_Expr_ForVars(function_dnf[i][j], rec_vars);
            for (auto name : rec_vars)
            {
                if (non_local_vars.count(name) == 0)
                {
                    function_dnf[i][j] = replace_expr_for_var(function_dnf[i][j], name, name + "_" + func->getNameAsString());
                    local_vars.insert(name + "_" + func->getNameAsString());
                }
            }
        }
    }
    TransitionSystem res;
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
                    var.alterVar(binop->getLHS(), NULL);
                    rec_transystem.add_vars(var, binop->getRHS());
                }
                else
                {
                    for (int k = 0; k < rec_transystem.Vars.size(); k++)
                    {
                        expr = Trans_Expr_by_CurVars(expr, rec_transystem.Vars[k]);
                        rec_transystem.inequality_DNF[k].push_back(expr);
                    }
                }
            }
            else
            {
                LOG_WARNING("Unexpected Expr Type: " + string(expr->getStmtClassName()));
                exit(-1);
            }
        }
        res = Merge_Transystem(res, rec_transystem);
    }
    *this = res;
    return local_vars;
}

void TransitionSystem::Merge_IneqDNF(vector<vector<Expr *>> &dnf)
{
    inequality_DNF = Merge_DNF(inequality_DNF, dnf);
    copy_after_update(dnf.size());
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
//             LOG_INFO(name);
//         for (int j = 0; j < dnf[i].size(); j++)
//         {
//             Expr *expr = dnf[i][j];
//             if (!isa<BinaryOperator>(expr))
//             {
//                 LOG_WARNING("Unexpected Expr Type: " + string(expr->getStmtClassName()));
//                 exit(-1);
//             }
//             BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
//             if (binop->getOpcode() != BO_EQ)
//                 continue;
//             int count = 0;
//             string rec_name;
//             for (const auto &name : node)
//             {
//                 if (Traverse_Expr_CheckVars(expr, possibles[name]))
//                 {
//                     count++;
//                     rec_name = name;
//                 }
//             }
//             if (count == 1)
//             {
//                 DeclRefExpr *left = createDeclRefExpr(rec_name);
//                 Expr *right_expr = Trans_LinExpr_to_Expr(Trans_Expr_to_LinExpr(binop->getLHS(), TransformationType::Loc, info->get_dimension()), rec_name);
//                 dnf[i][j] = createBinOp(left, right_expr, BO_Assign);
//             }
//             else if (count > 1)
//             {
//                 // TODO : Deal the different order, which possibly leads to such issues
//                 LOG_WARNING("Unexpected Situtation While possible left value count >=2");
//                 exit(-1);
//             }
//         }
//     }
// }

Expr *TransitionSystem::Trans_VariableInfo_to_Expr(VariableInfo var, bool init)
{
    // assert(var.getQualType().getAsString()=="int");
    Expr *initExpr = var.getVariableValue();
    string var_name = var.getVariableName();
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
vector<vector<Expr *>> Trans_Polys_to_Exprs(vector<C_Polyhedron *> poly, bool init_remove)
{
    vector<vector<Expr *>> res;
    for (int i = 0; i < poly.size(); i++)
    {
        C_Polyhedron *rec_poly = poly[i];
        vector<Expr *> exprs;
        if (init_remove)
            rec_poly->remove_higher_space_dimensions(int(info->get_dimension() / 2));
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
vector<vector<Expr *>> Trans_Polys_to_Exprs(vector<C_Polyhedron> poly, bool init_remove)
{
    vector<vector<Expr *>> res;
    for (int i = 0; i < poly.size(); i++)
    {
        C_Polyhedron rec_poly = poly[i];
        vector<Expr *> exprs;
        if (init_remove)
            rec_poly.remove_higher_space_dimensions(int(info->get_dimension() / 2));
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

void TransitionSystem::In_Loop()
{
    InWhileLoop = true;
    DNF.clear();
    Vars.clear();
    inequality_DNF.clear();
    DNF.resize(1);
    Vars.resize(1);
    inequality_DNF.resize(1);
    return;
}

unordered_set<string> TransitionSystem::get_Used_Vars(Expr *cond, Expr *increment)
{
    unordered_set<string> used_vars;
    for (int i = 0; i < DNF.size(); i++)
    {
        for (int j = 0; j < DNF[i].size(); j++)
        {
            Traverse_Expr_ForVars(DNF[i][j], used_vars);
        }
    }
    for (int i = 0; i < inequality_DNF.size(); i++)
    {
        for (int j = 0; j < inequality_DNF[i].size(); j++)
        {
            Traverse_Expr_ForVars(inequality_DNF[i][j], used_vars);
        }
    }
    Traverse_Expr_ForVars(cond, used_vars);
    Traverse_Expr_ForVars(increment, used_vars);
    return used_vars;
}

void TransitionSystem::copy_after_update(int size)
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

void TransitionSystem::Merge_Comments(vector<ACSLComment *> &comment)
{
    comments.insert(comments.end(), comment.begin(), comment.end());
    return;
}
void TransitionSystem::Merge_condition(Expr *condition, bool updated)
{
    vector<vector<Expr *>> exprs;
    exprs = Deal_with_condition(condition, true, exprs);
    copy_after_update(exprs.size());
    if (!updated)
    {
        vector<vector<Expr *>> new_inequailty_dnf;
        for (int i = 0; i < exprs.size(); i++)
        {
            for (int j = 0; j < inequality_DNF.size(); j++)
            {
                vector<Expr *> rec_dnf;
                rec_dnf.insert(rec_dnf.end(), inequality_DNF[j].begin(), inequality_DNF[j].end());
                for (int k = 0; k < exprs[i].size(); k++)
                {
                    rec_dnf.push_back(Trans_Expr_by_CurVars(exprs[i][k], Vars[j]));
                }
                new_inequailty_dnf.push_back(rec_dnf);
            }
        }
        inequality_DNF = new_inequailty_dnf;
    }
    else
        inequality_DNF = Merge_DNF(inequality_DNF, exprs);
    return;
}

TransitionSystem TransitionSystem::Merge_Transystem(TransitionSystem &left_trans, TransitionSystem &right_trans)
{
    // TODO: consider the situation of nested loop.
    TransitionSystem transystem;
    transystem.inequality_DNF = Connect_DNF(left_trans.inequality_DNF, right_trans.inequality_DNF);
    transystem.DNF = Connect_DNF(left_trans.DNF, right_trans.DNF);
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
    unordered_set<string> used_vars;
    used_vars.insert(var_name);
    for (int i = 0; i < DNF.size(); i++)
    {
        for (int j = 0; j < DNF[i].size(); j++)
        {
            if (Traverse_Expr_CheckVar(DNF[i][j], used_vars))
            {
                DNF[i].erase(DNF[i].begin() + j);
                j--;
            }
        }
    }
    for (int i = 0; i < inequality_DNF.size(); i++)
    {
        for (int j = 0; j < inequality_DNF[i].size(); j++)
        {
            if (Traverse_Expr_CheckVar(inequality_DNF[i][j], used_vars))
            {
                inequality_DNF[i].erase(inequality_DNF[i].begin() + j);
                j--;
            }
        }
    }
    return;
}
void TransitionSystem::Update_Vars(bool init)
{
    if (DNF.size() != Vars.size())
    {
        LOG_WARNING("Unexpected size of DNF and Vars: " + to_string(DNF.size()) + " and " + to_string(Vars.size()));
        exit(-1);
    }

    for (int i = 0; i < Vars.size(); i++)
    {
        for (int j = 0; j < Vars[i].size(); j++)
        {
            Expr *assign_expr;
            assign_expr = Trans_VariableInfo_to_Expr(Vars[i][j], init);
            if (assign_expr)
                DNF[i].push_back(assign_expr);
        }
    }
    return;
}

void TransitionSystem::deduplicate(vector<vector<Expr *>> &dnf)
{
    unordered_set<string> used_vars;
    for (int i = 0; i < dnf.size(); i++)
    {
        for (int j = 0; j < dnf[i].size(); j++)
        {
            Traverse_Expr_ForVars(dnf[i][j], used_vars);
        }
    }
    var_info *rec_info = new var_info(info);
    if (info)
    {
        delete info;
        info = NULL;
    }
    else
        rec_info = NULL;
    info = new var_info();
    for (auto name : used_vars)
        info->search_and_insert(name.c_str());
    for (int i = 0; i < dnf.size(); i++)
    {
        C_Polyhedron *p = new C_Polyhedron(info->get_dimension(), UNIVERSE);
        for (int j = 0; j < dnf[i].size(); j++)
        {
            p->add_constraints(*Trans_Expr_to_Constraints(dnf[i][j], TransformationType::Loc, info->get_dimension()));
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
vector<vector<Expr *>> TransitionSystem::Deal_with_condition(Expr *condition, bool logic)
{
    vector<vector<Expr *>> cur;
    return Deal_with_condition(condition, logic, cur);
}

vector<vector<Expr *>> TransitionSystem::Deal_with_condition(Expr *condition, bool logic, vector<vector<Expr *>> cur)
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
        else if (binop->getOpcode() == BO_NE)
        {
            if (logic)
            {
                BinaryOperator *binop_left = new (context) BinaryOperator(binop->getLHS(), binop->getRHS(), BO_LT, binop->getRHS()->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
                BinaryOperator *binop_right = new (context) BinaryOperator(binop->getLHS(), binop->getRHS(), BO_GT, binop->getRHS()->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
                left_expr = Deal_with_condition(binop_left, logic, cur);
                right_expr = Deal_with_condition(binop_right, logic, cur);
                return Connect_DNF(left_expr, right_expr);
            }
        }
        else if (binop->getOpcode() == BO_EQ)
        {
            if (!logic)
            {
                BinaryOperator *binop_left = new (context) BinaryOperator(binop->getLHS(), binop->getRHS(), BO_LT, binop->getRHS()->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
                BinaryOperator *binop_right = new (context) BinaryOperator(binop->getLHS(), binop->getRHS(), BO_GT, binop->getRHS()->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
                left_expr = Deal_with_condition(binop_left, !logic, cur);
                right_expr = Deal_with_condition(binop_right, !logic, cur);
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
    if (DeclRefExpr *decl = dyn_cast<DeclRefExpr>(condition))
    {
        return Deal_with_condition(createBinOp(decl, createIntegerLiteral(0), BO_NE), logic, cur);
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
                LOG_WARNING("Unexpected Opcode Type: " + string(binop->getOpcodeStr()));
                exit(-1);
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

Expr *replace_expr_for_var(Expr *expr, string origin_name, string new_name)
{
    if (!expr)
    {
        LOG_WARNING("expr is empty");
        exit(-1);
    }
    if (isa<BinaryOperator>(expr))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
        binop = createBinOp(replace_expr_for_var(binop->getLHS(), origin_name, new_name), replace_expr_for_var(binop->getRHS(), origin_name, new_name), binop->getOpcode());
        return binop;
    }
    else if (isa<DeclRefExpr>(expr))
    {
        DeclRefExpr *declRef = dyn_cast<DeclRefExpr>(expr);
        string name = declRef->getDecl()->getNameAsString();
        if (name == origin_name)
            declRef = createDeclRefExpr(new_name);
        return declRef;
    }
    else if (isa<ImplicitCastExpr>(expr))
    {
        ImplicitCastExpr *implict = dyn_cast<ImplicitCastExpr>(expr);
        return replace_expr_for_var(implict->getSubExpr(), origin_name, new_name);
    }
    else if (isa<UnaryOperator>(expr))
    {
        UnaryOperator *unop = dyn_cast<UnaryOperator>(expr);
        return replace_expr_for_var(unop->getSubExpr(), origin_name, new_name);
    }
    else if (isa<IntegerLiteral>(expr))
    {
    }
    else
    {
        LOG_INFO("unexpected type in replacement: " + string(expr->getStmtClassName()));
    }
    return expr;
}
Expr *TransitionSystem::Trans_Expr_by_CurVars(Expr *expr, vector<VariableInfo> &Vars)
{
    if (!expr)
    {
        LOG_WARNING("expr is empty");
        exit(-1);
    }
    if (isa<BinaryOperator>(expr))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
        binop = createBinOp(Trans_Expr_by_CurVars(binop->getLHS(), Vars), Trans_Expr_by_CurVars(binop->getRHS(), Vars), binop->getOpcode());
        return binop;
    }
    else if (isa<DeclRefExpr>(expr))
    {
        DeclRefExpr *declRef = dyn_cast<DeclRefExpr>(expr);
        string name = declRef->getDecl()->getNameAsString();
        VariableInfo var;
        QualType emptyType;
        var.alterVar(name, declRef, emptyType);
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
    LOG_INFO("Before Eliminate impossible path");
    Print_DNF();
    for (int i = 0; i < DNF.size(); i++)
    {
        C_Polyhedron *p = new C_Polyhedron(size * 2, UNIVERSE);
        for (int j = 0; j < DNF[i].size(); j++)
        {
            if (CheckBreakFlag(DNF[i][j]))
                continue;
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

void TransitionSystem::Initialize_Locations_and_Transitions(int locsize, int varsize, Expr *condition, int actual_size)
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
    guard.resize(inequality_DNF.size());
    guard_primed.resize(inequality_DNF.size());
    for (int i = 0; i < inequality_DNF.size(); i++)
    {
        for (int j = 0; j < inequality_DNF[i].size(); j++)
        {
            guard_primed[i].push_back(Trans_Expr_to_Constraints(inequality_DNF[i][j], TransformationType::Guard, varsize));
            guard[i].push_back(Trans_Expr_to_Constraints(inequality_DNF[i][j], TransformationType::Loc, varsize));
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
                if (!CheckBreakFlag(DNF[i][index]))
                    p->add_constraints(*Trans_Expr_to_Constraints(DNF[i][index], TransformationType::Trans, varsize));
            for (int index = 0; index < guard[i].size(); index++)
                p->add_constraints(*guard[i][index]);
            if (break_branch.find(i) != break_branch.end())
            {
                if (j != locsize - 1)
                    continue;
                trans_name = "Exit_Transition_from_" + to_string(i) + "by breakstmt";
                p->remove_higher_space_dimensions(actual_size);
                TransitionRelation *trans = new TransitionRelation(varsize, info, dual_info, lambda_info, trans_name);
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
                p->remove_higher_space_dimensions(actual_size);
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
                    q->remove_higher_space_dimensions(actual_size);
                    TransitionRelation *trans = new TransitionRelation(varsize, info, dual_info, lambda_info, trans_name);
                    trans->set_locs((*loclist)[i], (*loclist)[j]);
                    trans->set_relation(q);
                    trlist->push_back(trans);
                }
            }
        }
    }
}

void TransitionSystem::Compute_Loop_Invariant(Expr *condition, unordered_set<string> vars_in_dnf, vector<C_Polyhedron> init_polys, int actual_size)
{
    // DONE: delete the unused variables in init_dnf.
    // DONE: Transform every path into a transition from one path to another.
    // DONE: Construct Location and Transition, and get the inequality_DNF , then print.
    // DONE: add variable_init to info.
    // DONE: alter the mode of the Trans_Expr_to_Constraints
    if (comments.size() == 0)
    {
        LOG_WARNING("No Comments has been added to the transystem.");
        exit(-1);
    }
    ACSLComment *loop_comment = get_CurComment();

    Elimiate_Impossible_Path(info->get_dimension());
    int locsize = DNF.size() + 1;
    cout << locsize << endl;
    vector<vector<Expr *>> invariant;
    LOG_INFO(to_string(init_polys.size()));
    for (int i = 0; i < init_polys.size(); i++)
    {
        for (int j = 0; j < locsize; j++)
        {
            // TODO: Clarify that what should be clear and how to save the transition information to save time.
            // TODO: Further optimize the implementation of processing poly.
            // TODO: remove useless result.
            if (j == locsize - 1)
                continue;
            loclist = new vector<Location *>();
            trlist = new vector<TransitionRelation *>();
            Initialize_Locations_and_Transitions(locsize, info->get_dimension(), condition, actual_size);
            (*loclist)[j]->set_initial(init_polys[i]);
            Print_Location_and_Transition();
            Compute_Invariant_Frontend();
            vector<C_Polyhedron> loc_invariant = (*loclist)[locsize - 1]->get_vp_inv().get_vp();
            invariant = Connect_DNF(invariant, Trans_Polys_to_Exprs(loc_invariant, true));
            // Print_DNF(Trans_Polys_to_Exprs(loc_invariant));
            loop_comment->add_invariant(Trans_Polys_to_Exprs(loc_invariant, true), true);
            loc_invariant.clear();

            for (int index = 0; index < locsize - 1; index++)
            {
                loc_invariant.push_back((*loclist)[index]->get_invariant());
            }
            // Print_DNF(Trans_Polys_to_Exprs(loc_invariant));
            loop_comment->add_invariant(Trans_Polys_to_Exprs(loc_invariant, true), true);
            delete loclist, trlist;
        }
    }

    inequality_DNF = invariant;
    loop_comment->add_assign_vars(vars_in_dnf);
    return;
}

vector<vector<Expr *>> TransitionSystem::Out_Loop(Expr *cond, unordered_set<string> &used_vars, vector<vector<Expr *>> &init_DNF, vector<vector<Expr *>> &init_ineq_DNF, vector<vector<VariableInfo>> &init_vars, unordered_set<string> &local_vars)
{
    if (info && dual_info && lambda_info)
    {
        delete info, dual_info, lambda_info;
        info = NULL;
        dual_info = NULL;
        lambda_info = NULL;
    }
    info = new var_info();
    lambda_info = new var_info();
    dual_info = new var_info();
    LOG_INFO("Collect Loop Transition Relation");
    Print_DNF();
    for (int i = 0; i < init_DNF.size(); i++)
    {
        for (int j = 0; j < init_DNF[i].size(); j++)
        {
            if (Traverse_Expr_CheckVar(init_DNF[i][j], used_vars))
            {
                Traverse_Expr_ForVars(init_DNF[i][j], used_vars);
            }
        }
    }
    for (int i = 0; i < init_ineq_DNF.size(); i++)
    {
        for (int j = 0; j < init_ineq_DNF[i].size(); j++)
        {
            if (Traverse_Expr_CheckVar(init_ineq_DNF[i][j], used_vars))
            {
                Traverse_Expr_ForVars(init_ineq_DNF[i][j], used_vars);
            }
        }
    }
    unordered_set<string> rec_vars = used_vars;
    used_vars.clear();
    for (auto name : rec_vars)
    {
        
        if (local_vars.count(name) == 0)
        {
            used_vars.insert(name);
        }
    }
    for (const auto &var : used_vars)
    {
        info->search_and_insert(var.c_str());
    }
    for (const auto &var : used_vars)
    {
        info->search_and_insert((var + INITSUFFIX).c_str());
    }
    for (const auto &var : local_vars)
    {
        info->search_and_insert(var.c_str());
    }
    for (const auto &var : local_vars)
    {
        info->search_and_insert((var + INITSUFFIX).c_str());
    }
    vector<C_Polyhedron> init_polys = Compute_and_Eliminate_Init_Poly(rec_vars, cond, init_DNF, init_ineq_DNF, init_vars);
    ACSLComment *comment = get_CurComment();
    // DONE: add the remaining DNF into the comment.
    vector<vector<Expr *>> remain_DNF = Append_DNF(init_DNF, init_ineq_DNF);
    add_fundamental_expr(rec_vars);
    Print_DNF();
    exit(0);
    Compute_Loop_Invariant(cond, rec_vars, init_polys, used_vars.size() * 2);
    bool flag = false;
    for (int i = 0; i < remain_DNF.size(); i++)
    {
        if (remain_DNF[i].size() != 0)
        {
            flag = true;
            break;
        }
    }

    InWhileLoop = false;
    Vars.clear();
    DNF.clear();
    Verified_Loop_Count++;
    if (!flag)
        remain_DNF.clear();
    return remain_DNF;
}

void TransitionSystem::After_loop(vector<vector<Expr *>> &dnf, unordered_set<string> &used_vars)
{
    for (int i = 0; i < dnf.size(); i++)
    {
        for (int j = 0; j < dnf[i].size(); j++)
        {
            if (!Traverse_Expr_CheckVars(dnf[i][j], used_vars))
            {
                dnf[i].erase(dnf[i].begin() + j);
                j--;
            }
        }
    }
    inequality_DNF = Connect_DNF(inequality_DNF, dnf);
    DNF.resize(inequality_DNF.size());
    Vars.resize(inequality_DNF.size());
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
void TransitionSystem::Process_SkipDNF(vector<vector<Expr *>> &dnf)
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

unordered_set<string> DFS_VarGraph(int cur, unordered_set<string> &visited, vector<string> &node, map<string, int> &cor_index, VarGraph *graph)
{
    unordered_set<string> possibles;
    string cur_name = node[cur];
    visited.insert(cur_name);
    possibles.insert(cur_name);
    unordered_set<string> to = graph->edges[cur_name];
    for (const auto &to_name : to)
    {
        if (visited.find(to_name) != visited.end())
        {
            unordered_set<string> traverse_var = graph->possible_rv[to_name];
            possibles.insert(traverse_var.begin(), traverse_var.end());
            continue;
        }
        if (cor_index.find(to_name) == cor_index.end())
        {
            possibles.insert(to_name);
            continue;
        }
        unordered_set<string> traverse_var = DFS_VarGraph(cor_index[to_name], visited, node, cor_index, graph);
        possibles.insert(traverse_var.begin(), traverse_var.end());
    }
    graph->possible_rv[cur_name] = possibles;
    return possibles;
}

// void TransitionSystem::Construct_Graph()
// {
//     for (int i = 0; i < Vars.size(); i++)
//     {
//         VarGraph graph;
//         for (int j = 0; j < Vars[i].size(); j++)
//         {
//             unordered_set<string> used_vars;
//             Expr *expr = Vars[i][j].getVariableValue();
//             string var_name = Vars[i][j].getVariableName();
//             Traverse_Expr_ForVars(expr, used_vars);
//             graph.edges[var_name] = used_vars;
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
      inequality_DNF(other.inequality_DNF)
//   InWhileLoop(other.InWhileLoop),
//   Inner_Loop_Depth(other.Inner_Loop_Depth),
//   Inner_Loop_Count(other.Inner_Loop_Count)
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
            raw_string_ostream rso(str);
            DNF[i][j]->printPretty(rso, nullptr, Policy);
            rso.flush();
            outs() << str << "\n";
        }
        outs() << "DNF disjunctive clause " << i << " is printed.\n";
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
        outs() << "inequality_DNF disjunctive clause " << i << " is printed.\n";
    }
    return;
}

void TransitionSystem::init()
{
    inequality_DNF.resize(1);
    DNF.resize(1);
    Vars.resize(1);
    Verified_Loop_Count = 0;
    return;
}

void TransitionSystem::clear()
{
    DNF.clear();
    inequality_DNF.clear();
    Vars.clear();
    return;
}