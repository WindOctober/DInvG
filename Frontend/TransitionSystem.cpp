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
DeclRefExpr *createDeclRefExpr(string name)
{
    ASTContext *context = TransitionSystem::context;
    VarDecl *VD = VarDecl::Create(*context, context->getTranslationUnitDecl(), SourceLocation(), SourceLocation(), &context->Idents.get(name), context->IntTy, nullptr, SC_None);
    DeclRefExpr *RefExpr = new (context) DeclRefExpr(*context, VD, false, VD->getType(), VK_LValue, SourceLocation(), DeclarationNameLoc(), NOUR_None);
    return RefExpr;
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
            llvm::raw_string_ostream rso(str);
            DNF[i][j]->printPretty(rso, nullptr, Policy);
            rso.flush();
            outs() << str << "\n";
        }
        outs() << "DNF disjunctive clause " << i << " is printed.";
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
            llvm::raw_string_ostream rso(str);
            DNF[i][j]->printPretty(rso, nullptr, Policy);
            rso.flush();
            outs() << str << "\n";
        }
        outs() << "DNF disjunctive clause " << i << " is printed.";
    }
    return;
}

string Print_Expr(Expr *expr)
{
    PrintingPolicy Policy(TransitionSystem::context->getLangOpts());
    string str;
    llvm::raw_string_ostream rso(str);
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
                LOG_INFO(var.getVariableName().c_str());
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
        if (name.find(INITSUFFIX)!=name.npos){
            int index=name.find(INITSUFFIX);
            name.replace(index,strlen(INITSUFFIX),"");
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
    else
    {
        LOG_INFO("Unexpected Type in Function Traverse_Expr_ForVars :");
        LOG_INFO(Print_Expr(expr));
        exit(0);
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
        res.insert(declRef->getDecl()->getNameAsString());
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
    else
    {
        LOG_WARNING("Unexpected Type " + string(expr->getStmtClassName()));
        LOG_WARNING(Print_Expr(expr));
        exit(0);
    }
    return;
}
bool CheckInitSuffix(Expr *expr)
{
    if (isa<BinaryOperator>(expr))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
        bool flag = true;
        flag &= CheckInitSuffix(binop->getLHS());
        flag &= CheckInitSuffix(binop->getRHS());
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
    else
    {
        LOG_WARNING("Unexpected Type" + string(expr->getStmtClassName()));
        LOG_WARNING(Print_Expr(expr));
        exit(0);
    }
    return true;
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
        LOG_INFO(VD->getNameAsString());
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
    else
    {
        LOG_WARNING("Unexpected Type" + string(expr->getStmtClassName()));
        LOG_WARNING(Print_Expr(expr));
        exit(0);
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
        LOG_INFO(VD->getNameAsString());
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
        exit(0);
    }
    return expr;
}
vector<C_Polyhedron> Compute_and_Eliminate_Init_Poly(const unordered_set<string> &used_vars, Expr *condition, vector<vector<Expr *>> &init_DNF, vector<vector<Expr *>> &init_ineq_DNF, vector<vector<VariableInfo>> &init_vars)
{
    // TODO: deal with the situation that return size=0;
    // DONE: write the transformation from Constraint to Expression.
    // DONE: think the inequality init_value.
    vector<vector<Expr *>> DNF;
    ASTContext *context = TransitionSystem::context;
    DNF.resize(init_DNF.size());
    assert(init_DNF.size()==init_vars.size());
    for(int i=0;i<init_DNF.size();i++){
        unordered_set<string> rec_used;
        for(int j=0;j<init_vars[i].size();j++){
            if (init_vars[i][j].getVariableValue())
                rec_used.insert(init_vars[i][j].getVariableName());
        }
        for(auto name: used_vars){
            if (rec_used.count(name)==0){
                VarDecl *varA = VarDecl::Create(*context, context->getTranslationUnitDecl(), SourceLocation(), SourceLocation(), &context->Idents.get(name), context->IntTy, NULL, SC_None);
                VarDecl *varB = VarDecl::Create(*context, context->getTranslationUnitDecl(), SourceLocation(), SourceLocation(), &context->Idents.get(name), context->IntTy, NULL, SC_None);
                DeclRefExpr *DeclRefExpr_a = new (context) DeclRefExpr(*context, varA, false, context->IntTy,
                                                                    VK_LValue, SourceLocation());
                DeclRefExpr *DeclRefExpr_b = new (context) DeclRefExpr(*context, varB, false, context->IntTy,
                                                                    VK_LValue, SourceLocation());
                FPOptions default_option;
                DeclRefExpr_b = dyn_cast<DeclRefExpr>(Add_InitSuffix(DeclRefExpr_b));
                BinaryOperator *AssignStmt = new (context) BinaryOperator(DeclRefExpr_a, DeclRefExpr_b, BO_Assign,
                                                                        context->IntTy, VK_RValue,
                                                                        OK_Ordinary, SourceLocation(),
                                                                        default_option);
                for (int j = 0; j < DNF.size(); j++)
                {
                    DNF[j].push_back(AssignStmt);
                }
            }
        }
    }
    for (int i = 0; i < init_DNF.size(); i++)
    {
        for (int j = 0; j < init_DNF[i].size(); j++)
        {
            if (Traverse_Expr_CheckVars(init_DNF[i][j], used_vars))
            {
                if (isa<BinaryOperator>(init_DNF[i][j]))
                {
                    LOG_INFO(Print_Expr(init_DNF[i][j]));
                    BinaryOperator *binop = dyn_cast<BinaryOperator>(init_DNF[i][j]);
                }
                else
                    LOG_WARNING("Unexpected type of init_DNF.");

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
            if (Traverse_Expr_CheckVars(init_ineq_DNF[i][j], used_vars))
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
    DNF = Merge_DNF(DNF, ineq_DNF);
    
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

void TransitionSystem::Merge_IneqDNF(vector<vector<Expr *>> &dnf)
{
    inequality_DNF = Merge_DNF(inequality_DNF, dnf);
    return;
}
Expr *TransitionSystem::Trans_VariableInfo_to_Expr(VariableInfo var,bool init)
{
    // assert(var.getQualType().getAsString()=="int");
    Expr *initExpr = var.getVariableValue();
    VarDecl *VD;
    if (initExpr == NULL)
    {
        return NULL;
    }

    VD = VarDecl::Create(*context, context->getTranslationUnitDecl(), SourceLocation(), SourceLocation(), &context->Idents.get(var.getVariableName()), var.getQualType(), nullptr, SC_None);
    if (init)
        VD->setInit(Add_InitSuffix(initExpr));
    else
        VD->setInit(initExpr);
    DeclRefExpr *LHS = new (context) DeclRefExpr(*context, VD, false, VD->getType(), VK_LValue, SourceLocation(), DeclarationNameLoc(), NOUR_None);
    FPOptions default_options;
    Expr *expr = new (context) BinaryOperator(LHS, var.getVariableValue(), BO_Assign, var.getVariableValue()->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
    return expr;
}

vector<vector<Expr *>> Trans_Polys_to_Exprs(vector<C_Polyhedron> poly)
{
    vector<vector<Expr *>> res;
    for (int i = 0; i < poly.size(); i++)
    {
        C_Polyhedron rec_poly = poly[i];
        vector<Expr *> exprs;
        for (auto constraint : rec_poly.minimized_constraints())
        {
            exprs.push_back(Trans_Constraint_to_Expr(constraint));
        }
        res.push_back(exprs);
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
    Traverse_Expr_ForVars(cond, used_vars);
    Traverse_Expr_ForVars(increment, used_vars);
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
        for (int i = 0; i < exprs.size(); i++)
            for (int j = 0; j < exprs[i].size(); j++)
                exprs[i][j] = Trans_Expr_by_CurVars(exprs[i][j], Vars[i]);
    inequality_DNF = Merge_DNF(exprs, inequality_DNF);
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

void TransitionSystem::Update_Vars(bool init)
{
    if (DNF.size() != Vars.size())
        DNF.resize(Vars.size());
    for (int i = 0; i < Vars.size(); i++)
    {
        for (int j = 0; j < Vars[i].size(); j++)
        {
            Expr *assign_expr;
            assign_expr = Trans_VariableInfo_to_Expr(Vars[i][j],init);
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

void TransitionSystem::Initialize_Locations_and_Transitions(int locsize, int varsize, Expr *condition)
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

    Elimiate_Impossible_Path(info->get_dimension());
    int locsize = DNF.size() + 1;
    cout << locsize << endl;
    vector<vector<Expr *>> invariant;
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
            Initialize_Locations_and_Transitions(locsize, info->get_dimension(), condition);
            (*loclist)[j]->set_initial(init_polys[i]);
            Print_Location_and_Transition();
            Compute_Invariant_Frontend();
            vector<C_Polyhedron> loc_invariant = (*loclist)[locsize - 1]->get_vp_inv().get_vp();
            invariant = Connect_DNF(invariant, Trans_Polys_to_Exprs(loc_invariant));
            Print_DNF(Trans_Polys_to_Exprs(loc_invariant));
            loop_comment->add_invariant(Trans_Polys_to_Exprs(loc_invariant), true);
            loc_invariant.clear();

            for (int index = 0; index < locsize - 1; index++)
            {
                loc_invariant.push_back((*loclist)[index]->get_invariant());
            }
            // Print_DNF(Trans_Polys_to_Exprs(loc_invariant));
            loop_comment->add_invariant(Trans_Polys_to_Exprs(loc_invariant), true);
            delete loclist, trlist;
        }
    }

    inequality_DNF = invariant;
    loop_comment->add_assign_vars(vars_in_dnf);
    return;
}

void TransitionSystem::Out_Loop(Expr *cond, unordered_set<string> &used_vars, vector<vector<Expr *>> &init_DNF, vector<vector<Expr *>> &init_ineq_DNF, vector<vector<VariableInfo>> &init_vars)
{
    info = new var_info();
    lambda_info = new var_info();
    dual_info = new var_info();
    for (const auto &var : used_vars)
    {
        info->search_and_insert(var.c_str());
        info->search_and_insert((var + INITSUFFIX).c_str());
    }
    Print_DNF();
    vector<C_Polyhedron> init_polys = Compute_and_Eliminate_Init_Poly(used_vars, cond, init_DNF, init_ineq_DNF, init_vars);
    ACSLComment *comment = get_CurComment();
    // DONE: add the remaining DNF into the comment.
    vector<vector<Expr *>> remain_DNF = Append_DNF(init_DNF, init_ineq_DNF);
    Compute_Loop_Invariant(cond, used_vars, init_polys);

    if (remain_DNF.size())
        comment->add_invariant(remain_DNF, false);
    InWhileLoop = false;
    Vars.clear();
    DNF.clear();
    Vars.resize(inequality_DNF.size());
    DNF.resize(inequality_DNF.size());
    Verified_Loop_Count++;
    delete info, dual_info, lambda_info;
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

void TransitionSystem::init()
{
    inequality_DNF.resize(1);
    DNF.resize(1);
    Vars.resize(1);
    Verified_Loop_Count = 0;
    return;
}