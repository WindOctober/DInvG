#include "Library.hpp"
#include "CFGVisitor.hpp"
#include "var-info.h"
#include <unordered_set>
extern var_info *info;
void Log(const string &level, const string &function, int line, string msg)
{
    outs() << "\n[" << level << " " << function << ":" << line << "] " << msg;
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

vector<vector<Expr *>> Merge_DNF(vector<vector<Expr *>> left_expr, vector<vector<Expr *>> right_expr)
{
    if (left_expr.size() == 0)
        return right_expr;
    if (right_expr.size() == 0)
        return left_expr;
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

vector<vector<Expr *>> Connect_DNF(vector<vector<Expr *>> left_expr, vector<vector<Expr *>> right_expr)
{
    left_expr.insert(left_expr.end(), right_expr.begin(), right_expr.end());
    return left_expr;
}

vector<C_Polyhedron> Merge_Poly(vector<C_Polyhedron> &left_poly, vector<C_Polyhedron> &right_poly)
{
    // NOTE: keep an eye on the polyhedron's dimensions.
    vector<C_Polyhedron> res;
    if (right_poly.size() == 0)
        return left_poly;
    if (left_poly.size() == 0)
        return right_poly;
    for (int i = 0; i < left_poly.size(); i++)
    {
        for (int j = 0; j < right_poly.size(); j++)
        {
            C_Polyhedron poly(info->get_dimension(), UNIVERSE);
            poly.add_constraints(left_poly[i].minimized_constraints());
            poly.add_constraints(right_poly[j].minimized_constraints());
            if (!poly.is_empty())
            {
                res.push_back(poly);
            }
        }
    }
    return res;
}

// vector<vector<vector<string>>> Derive_Vars_From_Poly(vector<C_Polyhedron> &poly, vector<VariableInfo> &vars)
// {
//     vector<vector<vector<string>>> res;
//     res.resize(poly.size());
//     unordered_map<int, string> var_map;
//     for (int i = 0; i < vars.size(); i++)
//     {
//         int index = info->search(vars[i].getVariableName().c_str());
//         string name = vars[i].getVariableName();
//         var_map.insert(pair<int, string>(Variable(index).id(), name));
//     }
//     for (int i = 0; i < poly.size(); i++)
//     {
//         vector<vector<string>> used_vars;
//         Constraint_System constraints = poly[i].minimized_constraints();
//         for (auto &constraint : constraints)
//         {
//             const auto &le = constraint.expression();
//             vector<string> used;
//             for (auto it = le.begin(); it != le.end(); ++it)
//             {
//                 Variable var = it.variable();
//                 int var_id = var.id();
//                 if (var_map.find(var_id) != var_map.end())
//                 {
//                     used.push_back(var_map[var_id]);
//                 }
//                 else
//                 {
//                     LOG_WARNING("UnFounded Variable with var id is: " + to_string(var_id));
//                 }
//             }
//             used_vars.push_back(used);
//         }
//         res[i] = used_vars;
//     }
//     return res;
// }

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
        if (name.find(INITSUFFIX) == name.npos && coef != 0)
        {
            // TODO: only allow unsigned int or unsigned int, special deal with char* or string.
            VarDecl *VD = VarDecl::Create(*Context, Context->getTranslationUnitDecl(), SourceLocation(), SourceLocation(), &Context->Idents.get(name), Context->IntTy, nullptr, SC_None);
            DeclRefExpr *RefExpr = new (Context) DeclRefExpr(*Context, VD, false, VD->getType(), VK_LValue, SourceLocation(), DeclarationNameLoc(), NOUR_None);
            IntegerLiteral *Coef = IntegerLiteral::Create(*Context, APInt(32, abs(coef)), Context->IntTy, SourceLocation());
            BinaryOperator *multExpr = new (Context) BinaryOperator(Coef, RefExpr, BO_Mul, Context->IntTy, VK_RValue, OK_Ordinary, SourceLocation(), default_options);
            if (!res)
            {
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

bool Traverse_Expr_CheckVars(Expr *expr,const unordered_set<string> &res){
    bool flag=true;
    if (isa<BinaryOperator>(expr))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
        flag&=Traverse_Expr_CheckVars(binop->getLHS(), res);
        flag&=Traverse_Expr_CheckVars(binop->getRHS(), res);
    }
    else if (isa<DeclRefExpr>(expr))
    {
        DeclRefExpr *declRef = dyn_cast<DeclRefExpr>(expr);
        string name=declRef->getDecl()->getNameAsString();
        if (res.find(name)!=res.end())
            return true;
        else
            return false;
    }
    else if (isa<ImplicitCastExpr>(expr))
    {
        ImplicitCastExpr *implict = dyn_cast<ImplicitCastExpr>(expr);
        flag&=Traverse_Expr_CheckVars(implict->getSubExpr(), res);
    }
    else if (isa<IntegerLiteral>(expr))
    {

    }
    else
    {
        LOG_INFO("Unexpected Type in Function Traverse_Expr_ForVars :");
        LOG_INFO(Print_Expr(expr));
        exit(0);
    }
    return flag;
}

bool check_guard(Expr *expr)
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


void Traverse_Expr_ForVars(Expr *expr, unordered_set<string> &res)
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
    else
    {
        LOG_WARNING("Unexpected Type"+string(expr->getStmtClassName()));
        LOG_WARNING(Print_Expr(expr));
        exit(0);
    }
    return;
}

vector<C_Polyhedron> Compute_and_Eliminate_Init_Poly(const unordered_set<string>& used_vars, Expr *condition,vector<vector<Expr*>>& init_DNF,vector<vector<Expr*> > &init_ineq_DNF)
{
    // TODO: deal with the situation that return size=0;
    // DONE: write the transformation from Constraint to Expression.
    // DONE: think the inequality init_value.
    
    vector<vector<Expr*> > DNF;
    DNF.resize(init_DNF.size());
    for(int i=0;i<init_DNF.size();i++){
        for(int j=0;j<init_DNF[i].size();j++){
            if (Traverse_Expr_CheckVars(init_DNF[i][j],used_vars)){
                DNF[i].push_back(init_DNF[i][j]);
                init_DNF[i].erase(init_DNF[i].begin()+j);
                j--;
            }
        }
        if (init_DNF[i].size()==0){
            init_DNF.erase(init_DNF.begin()+i);
        }
        else if (DNF[i].size()==0){
            DNF.erase(DNF.begin()+i);
            i--;
        }
    }
    vector<vector<Expr*>> ineq_DNF;
    ineq_DNF.resize(init_ineq_DNF.size());
    for(int i=0;i<init_ineq_DNF.size();i++){
        for(int j=0;j<init_ineq_DNF[i].size();j++){
            if (!Traverse_Expr_CheckVars(init_ineq_DNF[i][j],used_vars)){
                ineq_DNF[i].push_back(init_ineq_DNF[i][j]);
                init_ineq_DNF[i].erase(init_ineq_DNF[i].begin()+j);
                j--;
            }
        }
        if (init_ineq_DNF[i].size()==0){
            init_ineq_DNF.erase(init_ineq_DNF.begin()+i);
        }
        else if (ineq_DNF[i].size()==0){
            ineq_DNF.erase(ineq_DNF.begin()+i);
            i--;
        }
    }
    DNF=Merge_DNF(DNF,ineq_DNF);
    vector<C_Polyhedron> init_polys;
    for (int i = 0; i < DNF.size(); i++)
    {
        C_Polyhedron *p = new C_Polyhedron(info->get_dimension(), UNIVERSE);
        for (int j = 0; j < DNF[i].size(); j++)
        {
            p->add_constraints(*Trans_Expr_to_Constraints(DNF[i][j], TransformationType::Loc, info->get_dimension()));
        }
        if (!p->is_empty())
            init_polys.push_back(*p);
    }
    return init_polys;
}