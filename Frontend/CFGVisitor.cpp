// DONE: alter the source code and generate a annotated version (with invariant annotations before the while loop)
// DONE: think how to solve the inter-procedural invariant.
#include "CFGVisitor.hpp"
#include "TransitionSystem.hpp"
#include "Library.hpp"
#include <iostream>
#include <memory>
#include <fstream>
#include "var-info.h"
#include <string>
extern ifstream infile;
extern ofstream outfile;
set<string> Main_Functions;
set<string> Visited_Functions;
extern var_info *info;
unordered_set<string> global_vars;
void CFGVisitor::Terminate_errors(enum ErrorType Errors)
{
    switch (Errors)
    {
    case ErrorType::FloatVarError:
        errs() << "CFGVisitor::Terminate_errors FloatVarError";
        return;
    case ErrorType::CFGInitError:
        errs() << "CFGVisitor::Terminate_errors CFGInitError";
        return;
    case ErrorType::UnexpectedTypeError:
        errs() << "CFGVisitor::Terminate_errors UnexpectedType";
        return;
    case ErrorType::VarDeclUnFoundError:
        errs() << "CFGVisitor::Terminate_errors VarDeclUnFoundError";
        return;
    case ErrorType::CalleeUnFoundError:
        errs() << "CFGVisitor::Terminate_errors CalleeUnFoundError";
        return;
    }
    errs() << "CFGVisitor::Terminate_errors UnknownError";
    return;
}

string CFGVisitor::create_name(string base)
{
    global_conflict_index++;
    string Name = base + to_string(global_conflict_index);
    return Name;
}

Expr *CFGVisitor::preprocess_expr(Expr *expr, TransitionSystem &transystem)
{
    if (isa<BinaryOperator>(expr))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
        binop->setLHS(preprocess_expr(binop->getLHS(), transystem));
        binop->setRHS(preprocess_expr(binop->getRHS(), transystem));
        return binop;
    }
    if (isa<UnaryOperator>(expr))
    {
        UnaryOperator *unop = dyn_cast<UnaryOperator>(expr);
        if (unop->getOpcode() != UO_Deref)
            unop->setSubExpr(preprocess_expr(unop->getSubExpr(), transystem));
        else
        {
            Expr *subexpr = unop->getSubExpr();
            if (isa<ImplicitCastExpr>(subexpr))
            {
                ImplicitCastExpr *implicit = dyn_cast<ImplicitCastExpr>(subexpr);
                subexpr = implicit->getSubExpr();
            }
            if (isa<DeclRefExpr>(subexpr))
            {
                DeclRefExpr *ref = dyn_cast<DeclRefExpr>(subexpr);
                ref = createDeclRefExpr("*" + ref->getDecl()->getNameAsString());
                return ref;
            }
            else
            {
                LOG_WARNING("Unexpected UnaryOperator Type: " + string(subexpr->getStmtClassName()));
                exit(0);
            }
        }
        return unop;
    }
    if (isa<ImplicitCastExpr>(expr))
    {
        ImplicitCastExpr *implicit = dyn_cast<ImplicitCastExpr>(expr);
        implicit->setSubExpr(preprocess_expr(implicit->getSubExpr(), transystem));
        return implicit;
    }
    if (isa<DeclRefExpr>(expr))
    {
        return expr;
    }
    if (isa<IntegerLiteral>(expr))
    {
        return expr;
    }
    if (isa<ParenExpr>(expr))
    {
        ParenExpr *paren = dyn_cast<ParenExpr>(expr);
        paren->setSubExpr(preprocess_expr(paren->getSubExpr(), transystem));
        return paren;
    }
    if (isa<CallExpr>(expr))
    {
        string return_name;
        DealWithCallExpr(dyn_cast<CallExpr>(expr), transystem, return_name);
        return createDeclRefExpr(return_name);
    }
    LOG_WARNING("Unexpected Expr Type: " + string(expr->getStmtClassName()));
    exit(0);
}
void CFGVisitor::DealWithVarDecl(VarDecl *vardecl, TransitionSystem &transystem)
{
    VariableInfo var;
    if (vardecl == NULL)
        Terminate_errors(ErrorType::VarDeclUnFoundError);
    // Deal with pointer, pure numeric, arrays.
    QualType stmt_type = vardecl->getType();
    string var_name = vardecl->getName();

    if (stmt_type->isArrayType())
    {
    }
    else if (stmt_type->isPointerType())
    {
        QualType pointer_type = stmt_type->getPointeeType();
        if (pointer_type->isFloatingType())
        {
            LOG_WARNING("Pointer type is floating!");
            exit(0);
        }
        Stmt *init = vardecl->getInit();
        if (isa<ImplicitCastExpr>(init))
        {
            ImplicitCastExpr *implicit = dyn_cast<ImplicitCastExpr>(init);
            Expr *expr = implicit->getSubExpr();
            if (isa<CallExpr>(expr))
            {
                CallExpr *call = dyn_cast<CallExpr>(expr);
                // NOTE: Assume Malloc is right, this tool do not check the mem safety.
                FunctionDecl *func = call->getDirectCallee();
                string name = func->getNameAsString();
                if (name == "malloc")
                {
                    LOG_INFO("Variable " + var_name + " is allocated.");
                    var.alterVar("*" + var_name, NULL, stmt_type);
                }
                else
                {
                    LOG_WARNING("Unsupported Function Call While initializing the variable");
                    LOG_WARNING("function name is: " + name);
                    exit(0);
                }
            }
            else
            {
                LOG_INFO(expr->getStmtClassName());
            }
        }
        else
        {
            LOG_INFO(init->getStmtClassName());
        }
    }
    else if (stmt_type->isUnsignedIntegerType())
    {
        var.alterVar(var_name, vardecl->getInit(), stmt_type);
        FPOptions default_options;
        DeclRefExpr *decl = createDeclRefExpr(var_name);
        IntegerLiteral *zero = IntegerLiteral::Create(*context, APInt(32, 0), context->IntTy, SourceLocation());
        BinaryOperator *constraint = new (context) BinaryOperator(decl, zero, BO_GE, stmt_type, VK_RValue, OK_Ordinary, SourceLocation(), default_options);
        transystem.add_expr(constraint);
    }
    else if (stmt_type->isIntegerType())
    {
        var.alterVar(var_name, vardecl->getInit(), stmt_type);
    }
    else if (stmt_type->isBooleanType())
    {
        var.alterVar(var_name, vardecl->getInit(), stmt_type);
    }
    else if (stmt_type->isFloatingType())
        Terminate_errors(ErrorType::FloatVarError);
    transystem.add_vars(var);
}

void CFGVisitor::DealWithUnaryOp(UnaryOperator *stmt, TransitionSystem &transystem)
{
    Expr *res;
    Expr *left_value = stmt->getSubExpr();
    FPOptions default_options;
    if (stmt->getOpcode() == UO_PreDec || stmt->getOpcode() == UO_PostDec)
    {
        IntegerLiteral *one = IntegerLiteral::Create(*context, APInt(32, 1), context->IntTy, SourceLocation());
        BinaryOperator *minusOne = new (context) BinaryOperator(left_value, one, BO_Sub, left_value->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
        res = new (*context) BinaryOperator(left_value, minusOne, BO_Assign, left_value->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
        DealWithBinaryOp(dyn_cast<BinaryOperator>(res), transystem);
    }
    else if (stmt->getOpcode() == UO_PreInc || stmt->getOpcode() == UO_PostInc)
    {
        IntegerLiteral *one = IntegerLiteral::Create(*context, APInt(32, 1), context->IntTy, SourceLocation());
        BinaryOperator *plusOne = new (context) BinaryOperator(left_value, one, BO_Add, left_value->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
        res = new (*context) BinaryOperator(left_value, plusOne, BO_Assign, left_value->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
        DealWithBinaryOp(dyn_cast<BinaryOperator>(res), transystem);
    }
    return;
}

void CFGVisitor::DealWithBinaryOp(BinaryOperator *stmt, TransitionSystem &transystem)
{
    Expr *res;
    FPOptions default_options;
    if (stmt->getOpcode() == BO_Assign)
    {
        VariableInfo var;
        Expr *expr = stmt->getLHS();
        var.alterVar(stmt->getLHS(), NULL);
        transystem.add_vars(var, preprocess_expr(stmt->getRHS(), transystem));
    }
    return;
}

void CFGVisitor::DealWithFunctionDecl(FunctionDecl *stmt, TransitionSystem &transystem)
{
}

void CFGVisitor::DealWithCallExpr(CallExpr *callexpr, TransitionSystem &transystem, string &return_value)
{
    FunctionDecl *CallFunction = callexpr->getDirectCallee();
    SourceManager &SM = context->getSourceManager();
    string FuncName = CallFunction->getNameAsString();
    if (FuncName == "__CPROVER_assume")
    {
        assert(callexpr->getNumArgs() == 1);
        transystem.Merge_condition(callexpr->getArg(0), true);
    }
    else
    {
        if (!SM.isInMainFile(CallFunction->getLocation()))
        {
            LOG_INFO("Visit Unexpected outer-defined function" + FuncName);
            exit(-1);
        }
        LOG_INFO("Function Name:" + FuncName);
        if (verified_funcs.count(FuncName) == 0)
        {
            LOG_INFO("Visit Function:" + FuncName);
            VisitFunctionDecl(CallFunction);
        }
        vector<vector<Expr *>> function_dnf = dnf_for_funcs[FuncName];
        if (function_dnf.size() != 0)
        {
            for(int i=0;i<function_dnf.size();i++){
                for(int j=0;j<function_dnf[i].size();j++){
                    Expr* expr=function_dnf[i][j];
                    if (isa<BinaryOperator>(expr)){
                        BinaryOperator *binop=dyn_cast<BinaryOperator>(expr);
                        if (binop->getOpcode()!=BO_Assign) continue;
                        DealWithBinaryOp(binop,transystem);
                        function_dnf[i].erase(function_dnf[i].begin()+j);
                        j--;
                    }
                }
            }
            transystem.Merge_IneqDNF(function_dnf);
            return_value = FuncName + "_RetVal";
            LOG_INFO("After Merge Function Call");
            transystem.Print_DNF();
        }
        else
        {
            LOG_WARNING("No DNF for this function: " + FuncName);
            exit(-1);
        }
    }
}

bool CFGVisitor::DealWithStmt(Stmt *stmt, TransitionSystem &transystem, FunctionDecl *func)
{
    // Deal with the whole Stmt in code. (which usually means the complete statement in one line.)

    // DONE: Deal with assignment statement in code.
    // DONE: Deal with If statement in code.
    // DONE: Deal with For loop in code.
    // DONE: Deal with the situation of continue and break in code. [hint: consider the guard to break to be loop guard in break situation and the standalone branch cutted in continue statement]
    // TODO: Deal with special cases likes x=(a==b), y=(a>=b), which should be handled to if (a==b) x=1 else x=0 and so on.
    // DONE: Deal with the return statement in loop.
    PrintStmtInfo(stmt);
    if (isa<IfStmt>(stmt))
    {
        IfStmt *ifStmt = dyn_cast<IfStmt>(stmt);
        Expr *condition = ifStmt->getCond();
        Stmt *then_branch = ifStmt->getThen();
        Stmt *else_branch = ifStmt->getElse();
        vector<vector<Expr *>> ineq_dnf = transystem.get_IneqDNF();
        vector<ACSLComment *> rec_comments = transystem.get_Comments();
        transystem.clear_ineqDNF();
        TransitionSystem ElseTransystem(transystem);
        TransitionSystem ThenTransystem(transystem);
        ThenTransystem.Merge_condition(condition, false);
        ElseTransystem.Merge_condition(NegateExpr(condition), true);
        if (CompoundStmt *compound = dyn_cast<CompoundStmt>(then_branch))
        {
            for (auto stmt : compound->body())
            {
                bool flag = DealWithStmt(stmt, ThenTransystem, func);
                if (!flag)
                    break;
            }
        }
        if (CompoundStmt *compound = dyn_cast<CompoundStmt>(else_branch))
        {
            for (auto stmt : compound->body())
            {
                bool flag = DealWithStmt(stmt, ElseTransystem, func);
                if (!flag)
                    break;
            }
        }

        transystem = TransitionSystem::Merge_Transystem(ThenTransystem, ElseTransystem);
        transystem.Merge_IneqDNF(ineq_dnf);
        transystem.Merge_Comments(rec_comments);
    }
    else if (isa<ForStmt>(stmt) || isa<WhileStmt>(stmt))
    {
        vector<vector<Expr *>> remain_DNF;
        bool flag;
        Expr *loop_condition;
        Stmt *loop_body;
        SourceRange sourceRange;
        Expr *inc = NULL;
        if (isa<ForStmt>(stmt))
        {
            flag = true;
            ForStmt *forstmt = dyn_cast<ForStmt>(stmt);
            DealWithStmt(forstmt->getInit(), transystem, func);
            loop_condition = preprocess_expr(forstmt->getCond(), transystem);
            loop_body = forstmt->getBody();
            sourceRange = forstmt->getSourceRange();
            inc = preprocess_expr(forstmt->getInc(), transystem);
        }
        else
        {
            flag = false;
            WhileStmt *whileStmt = dyn_cast<WhileStmt>(stmt);
            loop_condition = preprocess_expr(whileStmt->getCond(), transystem);
            loop_body = whileStmt->getBody();
            sourceRange = whileStmt->getSourceRange();
        }
        unordered_set<string> used_vars;
        transystem.Update_Vars(true);
        LOG_INFO("After collect initial DNF information: ");
        transystem.Print_DNF();
        vector<vector<Expr *>> SkipLoop = transystem.Deal_with_condition(loop_condition, false);
        SkipLoop = Merge_DNF(SkipLoop, Append_DNF(transystem.get_DNF(), transystem.get_IneqDNF()));

        transystem.Merge_condition(loop_condition, true);
        vector<vector<Expr *>> init_DNF = transystem.get_DNF();
        vector<vector<Expr *>> init_ineq_DNF = transystem.get_IneqDNF();
        vector<vector<VariableInfo>> init_Vars = transystem.get_Vars();
        SourceLocation startLocation = sourceRange.getBegin();
        SourceManager &sourceManager = context->getSourceManager();
        int lineNumber = sourceManager.getSpellingLineNumber(startLocation);
        ACSLComment *loop_comment = new ACSLComment(lineNumber, ACSLComment::CommentType::LOOP);
        transystem.add_comment(loop_comment);
        transystem.In_Loop();
        transystem.Merge_condition(loop_condition, true);
        transystem.Print_DNF();

        if (CompoundStmt *compound = dyn_cast<CompoundStmt>(loop_body))
        {
            for (auto stmt : compound->body())
            {
                bool continue_flag = DealWithStmt(stmt, transystem, func);
                if (!continue_flag)
                    break;
            }
            if (flag)
                DealWithStmt(inc, transystem, func);
            transystem.Update_Vars(false);
            used_vars = transystem.get_Used_Vars(loop_condition, inc);
        }

        remain_DNF = transystem.Out_Loop(loop_condition, used_vars, init_DNF, init_ineq_DNF, init_Vars);
        transystem.Process_SkipDNF(SkipLoop);
        Print_DNF(SkipLoop);
        transystem.After_loop(SkipLoop, used_vars);
        loop_comment->add_invariant(SkipLoop, true);
        loop_comment->deduplication();
        loop_comment->add_invariant(remain_DNF, false);
        LOG_INFO("Remained DNF:");
        Print_DNF(remain_DNF);
        transystem.deduplicate(loop_comment->get_invariant());
    }
    else if (isa<DeclStmt>(stmt))
    {
        DeclStmt *declStmt = dyn_cast<DeclStmt>(stmt);

        for (auto *decl : declStmt->decls())
        {
            if (isa<VarDecl>(decl))
            {
                DealWithVarDecl(dyn_cast<VarDecl>(decl), transystem);
            }
            else if (isa<FunctionDecl>(decl))
            {
                DealWithFunctionDecl(dyn_cast<FunctionDecl>(decl), transystem);
            }
        }
    }
    else if (isa<BinaryOperator>(stmt))
    {
        DealWithBinaryOp(dyn_cast<BinaryOperator>(stmt), transystem);
    }
    else if (isa<ParenExpr>(stmt))
    {
        ParenExpr *expr = dyn_cast<ParenExpr>(stmt);
    }
    else if (isa<UnaryOperator>(stmt))
    {
        DealWithUnaryOp(dyn_cast<UnaryOperator>(stmt), transystem);
    }
    else if (isa<ContinueStmt>(stmt))
    {
        return false;
    }
    else if (isa<BreakStmt>(stmt))
    {
        DeclRefExpr *breakflag = createDeclRefExpr("break");
        transystem.add_expr(breakflag);
        return false;
    }
    else if (isa<CallExpr>(stmt))
    {
        CallExpr *call = dyn_cast<CallExpr>(stmt);
        string ReturnValue;
        DealWithCallExpr(call, transystem, ReturnValue);
        transystem.delete_expr_by_var(ReturnValue);
        LOG_INFO(ReturnValue);
    }
    else if (isa<ReturnStmt>(stmt))
    {
        // DONE: When Exit, record current DNF and ineq_DNF (update var)
        ReturnStmt *ret = dyn_cast<ReturnStmt>(stmt);
        transystem.Update_Vars(false);
        transystem.Construct_Graph();
        vector<vector<Expr *>> return_dnf;
        string func_name = func->getNameAsString();
        return_dnf = Append_DNF(transystem.get_IneqDNF(), transystem.get_DNF());
        if (verified_funcs.count(func_name) == 0)
        {
            verified_funcs.insert(func_name);
            string return_name = func_name + "_RetVal";
            DeclRefExpr *returnExpr = createDeclRefExpr(return_name);
            Expr *returnValue = ret->getRetValue();
            returnValue = createBinOp(returnExpr, returnValue,BO_Assign);
            for (int i = 0; i < return_dnf.size(); i++)
            {
                return_dnf[i].push_back(returnValue);
            }
            unordered_set<string> used_vars;
            unordered_set<string> total_vars;

            used_vars.insert(return_name);
            for (auto name : global_vars)
            {
                used_vars.insert(name);
            }
            for (auto it = func->param_begin(); it != func->param_end(); it++)
            {
                ParmVarDecl *param = *it;
                used_vars.insert(param->getNameAsString());
            }
            for (int i = 0; i < return_dnf.size(); i++)
            {
                for (int j = 0; j < return_dnf[i].size(); j++)
                {
                    Traverse_Expr_ForVars(return_dnf[i][j], total_vars);
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
                info->insert(name.c_str());
            for (auto name : total_vars)
                info->search_and_insert(name.c_str());
            vector<C_Polyhedron *> polys;
            for (int i = 0; i < return_dnf.size(); i++)
            {
                C_Polyhedron *p = new C_Polyhedron(info->get_dimension(), UNIVERSE);
                for (int j = 0; j < return_dnf[i].size(); j++)
                {
                    p->add_constraints(*Trans_Expr_to_Constraints(return_dnf[i][j], TransformationType::Loc, info->get_dimension()));
                }
                if (p->is_empty())
                {
                    LOG_WARNING("Unexpected empty polyhedron when process function");
                    exit(-1);
                }
                p->remove_higher_space_dimensions(used_vars.size());
                polys.push_back(p);
            }
            return_dnf = Trans_Polys_to_Exprs(polys, false);
            transystem.recover_dnf(return_dnf);
            delete info;
            info = rec_info;
            dnf_for_funcs[func_name] = return_dnf;
        }
        else
        {
            LOG_WARNING("Duplicate function visit.");
            exit(-1);
        }
        LOG_INFO("record function: " + func_name + " of which dnf is :");
        Print_DNF(return_dnf);
        return false;
    }
    return true;
}

bool CFGVisitor::VisitCallExpr(CallExpr *CE)
{
    if (VS != VisitorState::Main)
        return true;
    FunctionDecl *callee = CE->getDirectCallee();
    if (!callee)
        Terminate_errors(ErrorType::CalleeUnFoundError);
    SourceManager &SM = context->getSourceManager();
    if (!SM.isInMainFile(callee->getLocation()))
        return true;
    if (Visited_Functions.count(callee->getNameAsString()) == 0)
    {
        Visited_Functions.insert(callee->getNameAsString());
        outs() << "CalleeFunction:" << callee->getNameAsString() << "\n";
    }
    return true;
}

bool CFGVisitor::VisitVarDecl(VarDecl *var)
{
    if (VS != VisitorState::Collect_All_Function)
        return true;
    if (var->hasGlobalStorage() && !var->isStaticLocal())
    {
        global_vars.insert(var->getNameAsString());
    }
    return true;
}

bool CFGVisitor::VisitFunctionDecl(FunctionDecl *func)
{
    TransitionSystem::context = context;
    SourceManager &SM = context->getSourceManager();
    if (!SM.isInMainFile(func->getLocation()))
        return true;
    if (VS == VisitorState::Collect_All_Function)
    {
        Main_Functions.insert(func->getNameAsString());
        return true;
    }
    if (verified_funcs.count(func->getNameAsString()) != 0)
        return true;

    TransitionSystem transystem;
    transystem.init();
    Stmt *func_body = func->getBody();
    if (CompoundStmt *compound = dyn_cast<CompoundStmt>(func_body))
    {
        for (auto stmt : compound->body())
        {
            bool flag = DealWithStmt(stmt, transystem, func);
            if (!flag)
                break;
        }
    }
    add_comments(transystem.get_Comments());
    return true;
}

void CFGVisitor::PrintStmtInfo(Stmt *stmt)
{
    // TODO: complete this function case by case
    outs() << "\n";
    outs() << "[print statement info]" << '\n';
    outs() << stmt->getStmtClassName() << '\n';
    if (isa<IfStmt>(stmt))
    {
    }
    else if (isa<ForStmt>(stmt))
    {
    }
    else if (isa<WhileStmt>(stmt))
    {
    }
    else if (isa<DeclStmt>(stmt))
    {
        DeclStmt *declStmt = dyn_cast<DeclStmt>(stmt);
        for (auto *decl : declStmt->decls())
        {
            if (isa<VarDecl>(decl))
            {
                VarDecl *var = dyn_cast<VarDecl>(decl);
                QualType type = var->getType();
                outs() << "\t[VarType] " << type.getAsString() << "\n";
                outs() << "\t[name]" << var->getNameAsString() << '\n';
            }
            else if (isa<FunctionDecl>(decl))
            {
                // dyn_cast<FunctionDecl>(decl);
            }
        }
    }
    else if (isa<BinaryOperator>(stmt))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(stmt);
        outs() << "binary operator:"
               << " ";
        outs() << binop->getLHS()->getStmtClassName() << " ";
        outs() << binop->getOpcodeStr() << " ";
        outs() << binop->getRHS()->getStmtClassName() << " ";
    }
    else if (isa<ParenExpr>(stmt))
    {
        ParenExpr *expr = dyn_cast<ParenExpr>(stmt);
        outs() << "paren expression: ";
        outs() << expr->getSubExpr()->getStmtClassName() << " ";
    }
    else if (isa<UnaryOperator>(stmt))
    {
        UnaryOperator *unop = dyn_cast<UnaryOperator>(stmt);
        outs() << "unary operator: ";
        outs() << unop->getSubExpr()->getStmtClassName() << " " << unop->getOpcodeStr(unop->getOpcode()) << ' ';
    }
}

void CFGVisitor::add_comments(vector<ACSLComment *> comment_vec)
{
    comments.insert(comments.end(), comment_vec.begin(), comment_vec.end());
    return;
}

void CFGVisitor::Dump_Annotated_file()
{
    int lineNumber = 0;
    string line;
    int index = 0;
    if (comments.size() == 0)
    {
        LOG_WARNING("No comments have been generated");
        exit(1);
    }
    int cur_lineno = comments[index]->get_line_number();
    while (getline(infile, line))
    {
        lineNumber++;
        if (lineNumber == cur_lineno)
        {
            comments[index]->dump(outfile, context);
            index++;
            if (index != comments.size())
            {
                cur_lineno = comments[index]->get_line_number();
            }
        }
        outfile << line << "\n";
    }
    return;
}