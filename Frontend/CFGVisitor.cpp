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
set<string> MainFuncs;
set<string> Visited_Functions;
extern var_info *info;
unordered_set<string> global_vars;
unordered_set<string> LocalVars;
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

Expr *CFGVisitor::PreprocessExpr(Expr *expr, TransitionSystem &transystem)
{
    if (!expr)
        return NULL;

    if (isa<BinaryOperator>(expr))
    {
        BinaryOperator *binop = dyn_cast<BinaryOperator>(expr);
        binop = createBinOp(PreprocessExpr(binop->getLHS(), transystem), PreprocessExpr(binop->getRHS(), transystem), binop->getOpcode());
        return binop;
    }
    if (isa<UnaryOperator>(expr))
    {
        UnaryOperator *unop = dyn_cast<UnaryOperator>(expr);
        if (unop->getOpcode() == UO_PreInc)
        {
            Expr *SubExpr = PreprocessExpr(unop->getSubExpr(), transystem);
            transystem.AddExpr(createBinOp(SubExpr, createBinOp(SubExpr, createIntegerLiteral(1), BO_Add), BO_Assign));
            return createBinOp(SubExpr, createIntegerLiteral(1), BO_Add);
        }
        if (unop->getOpcode() == UO_PreDec)
        {
            Expr *SubExpr = PreprocessExpr(unop->getSubExpr(), transystem);
            transystem.AddExpr(createBinOp(SubExpr, createBinOp(SubExpr, createIntegerLiteral(1), BO_Sub), BO_Assign));
            return createBinOp(SubExpr, createIntegerLiteral(1), BO_Sub);
        }
        if (unop->getOpcode() == UO_PostInc)
        {
            Expr *SubExpr = PreprocessExpr(unop->getSubExpr(), transystem);
            transystem.AddExpr(createBinOp(SubExpr, createBinOp(SubExpr, createIntegerLiteral(1), BO_Add), BO_Assign));
            return SubExpr;
        }
        if (unop->getOpcode() == UO_PostDec)
        {
            Expr *SubExpr = PreprocessExpr(unop->getSubExpr(), transystem);
            transystem.AddExpr(createBinOp(SubExpr, createBinOp(SubExpr, createIntegerLiteral(1), BO_Sub), BO_Assign));
            return SubExpr;
        }
        if (unop->getOpcode() != UO_Deref)
            unop->setSubExpr(PreprocessExpr(unop->getSubExpr(), transystem));
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
                LOGWARN("Unexpected UnaryOperator Type: " + string(subexpr->getStmtClassName()));
                exit(-1);
            }
        }
        return unop;
    }
    if (isa<ImplicitCastExpr>(expr))
    {
        ImplicitCastExpr *implicit = dyn_cast<ImplicitCastExpr>(expr);
        implicit->setSubExpr(PreprocessExpr(implicit->getSubExpr(), transystem));
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
        if (!isa<UnaryOperator>(paren->getSubExpr()))
        {
            paren->setSubExpr(PreprocessExpr(paren->getSubExpr(), transystem));
            return paren;
        }
        UnaryOperator *unop = dyn_cast<UnaryOperator>(paren->getSubExpr());
        if (unop->getOpcode() == UO_Deref)
            return PreprocessExpr(unop, transystem);
        else
        {
            LOGINFO("Paren Expr UnaryOpCode is: " + string(unop->getOpcodeStr(unop->getOpcode())));
            paren->setSubExpr(PreprocessExpr(paren->getSubExpr(), transystem));
            return paren;
        }
    }
    if (isa<CallExpr>(expr))
    {
        string return_name = "";
        DealWithCallExpr(dyn_cast<CallExpr>(expr), transystem, return_name);
        if (return_name != "")
            return createDeclRefExpr(return_name);
        else
            return NULL;
    }
    if (isa<ArraySubscriptExpr>(expr))
    {

        ArraySubscriptExpr *array = dyn_cast<ArraySubscriptExpr>(expr);
        Expr *IndexExpr = array->getIdx();
        Expr *BaseExpr = array->getBase();

        if (isa<ImplicitCastExpr>(BaseExpr))
            BaseExpr = (dyn_cast<ImplicitCastExpr>(BaseExpr))->getSubExpr();
        if (isa<ImplicitCastExpr>(IndexExpr))
            IndexExpr = (dyn_cast<ImplicitCastExpr>(IndexExpr))->getSubExpr();
        if (!isa<DeclRefExpr>(BaseExpr))
        {
            if (isa<ArraySubscriptExpr>(BaseExpr) || isa<MemberExpr>(BaseExpr))
            {
                PreprocessExpr(BaseExpr, transystem);
            }
            else
            {
                LOGWARN("Unexpected BaseExprType: " + string(BaseExpr->getStmtClassName()));
                exit(-1);
            }
        }
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
        else if (IndexExpr->isConstantInitializer(*context, false))
        {
        }
        else
        {
            LOGWARN("Unexpected Mode of Array:" + PrintExpr(IndexExpr));
        }
        return createDeclRefExpr(PrintExpr(expr));
    }
    if (isa<OpaqueValueExpr>(expr))
    {
        OpaqueValueExpr *opaque = dyn_cast<OpaqueValueExpr>(expr);
        return createDeclRefExpr("NULL");
    }
    if (isa<MemberExpr>(expr))
    {
        MemberExpr *member = dyn_cast<MemberExpr>(expr);
        member->setBase(PreprocessExpr(member->getBase(), transystem));
        LOGINFO(member->getMemberDecl()->getNameAsString());
        return createDeclRefExpr(PrintExpr(member));
    }
    LOGWARN("Unexpected Expr Type: " + string(expr->getStmtClassName()));
    exit(-1);
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
            LOGWARN("Pointer type is floating!");
            exit(-1);
        }
        Stmt *init = vardecl->getInit();
        if (init)
        {
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
                        LOGINFO("Variable " + var_name + " is allocated.");
                        var.assign("*" + var_name, NULL, stmt_type);
                    }
                    else
                    {
                        LOGWARN("Unsupported Function Call While initializing the variable");
                        LOGWARN("function name is: " + name);
                        exit(-1);
                    }
                }
                else
                {
                    LOGINFO(expr->getStmtClassName());
                    var.assign("*" + var_name, NULL, stmt_type);
                }
            }
            else
            {
                LOGINFO(init->getStmtClassName());
            }
        }
    }
    else if (stmt_type->isUnsignedIntegerType())
    {
        var.assign(var_name, vardecl->getInit(), stmt_type);
        FPOptions default_options;
        DeclRefExpr *decl = createDeclRefExpr(var_name);
        IntegerLiteral *zero = IntegerLiteral::Create(*context, APInt(32, 0), context->IntTy, SourceLocation());
        BinaryOperator *constraint = new (context) BinaryOperator(decl, zero, BO_GE, stmt_type, VK_RValue, OK_Ordinary, SourceLocation(), default_options);
        transystem.AddExpr(constraint);
    }
    else if (stmt_type->isIntegerType())
    {
        var.assign(var_name, PreprocessExpr(vardecl->getInit(), transystem), stmt_type);
    }
    else if (stmt_type->isBooleanType())
    {
        var.assign(var_name, vardecl->getInit(), stmt_type);
    }
    else if (stmt_type->isFloatingType())
        Terminate_errors(ErrorType::FloatVarError);
    transystem.AddVars(var);
}

void CFGVisitor::DealWithUnaryOp(UnaryOperator *expr, TransitionSystem &transystem)
{
    Expr *res;
    Expr *left_value = expr->getSubExpr();
    FPOptions default_options;
    if (expr->getOpcode() == UO_PreDec || expr->getOpcode() == UO_PostDec)
    {
        IntegerLiteral *one = createIntegerLiteral(1);
        BinaryOperator *minusOne = new (context) BinaryOperator(left_value, one, BO_Sub, left_value->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
        res = new (*context) BinaryOperator(left_value, minusOne, BO_Assign, left_value->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
        DealWithBinaryOp(dyn_cast<BinaryOperator>(res), transystem);
    }
    else if (expr->getOpcode() == UO_PreInc || expr->getOpcode() == UO_PostInc)
    {
        IntegerLiteral *one = createIntegerLiteral(1);
        BinaryOperator *plusOne = new (context) BinaryOperator(left_value, one, BO_Add, left_value->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
        res = new (*context) BinaryOperator(left_value, plusOne, BO_Assign, left_value->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
        DealWithBinaryOp(dyn_cast<BinaryOperator>(res), transystem);
    }
    return;
}

void CFGVisitor::DealWithBinaryOp(BinaryOperator *binop, TransitionSystem &transystem)
{
    if (binop->getOpcode() == BO_Assign)
    {
        VariableInfo var;
        Expr *expr = binop->getLHS();
        var.assign(binop->getLHS(), NULL);
        Expr *value = PreprocessExpr(binop->getRHS(), transystem);
        if (value)
            transystem.AddVars(var, value);
    }
    else
    {
        LOGWARN("Unexpected BinaryOperator Stmt with opcode: " + string(binop->getOpcodeStr()));
        LOGWARN(PrintExpr(binop));
        exit(-1);
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
        transystem.MergeCond(callexpr->getArg(0), true);
    }
    else if (FuncName == "__VERIFIER_nondet_int" || FuncName == "__VERIFIER_assert")
        return;
    else
    {
        if (!SM.isInMainFile(CallFunction->getLocation()))
        {
            LOGINFO("Visit Unexpected outer-defined function" + FuncName);
            exit(-1);
        }
        LOGINFO("Function Name:" + FuncName);
        if (VerifiedFunc.count(FuncName) == 0)
        {
            LOGINFO("Visit Function:" + FuncName);
            VisitFunctionDecl(CallFunction);
        }
        return_value = create_name(FuncName + "_RetVal");
        vector<vector<Expr *>> function_dnf = FuncsDNF[FuncName];
        LOGINFO("print callfunction " + FuncName + " 's dnf:");
        PrintDNF(function_dnf);
        if (function_dnf.size() != 0)
        {
            unordered_set<string> rec_vars = transystem.MergeFuncCall(function_dnf, callexpr, return_value, global_vars);
            LocalVars.insert(rec_vars.begin(), rec_vars.end());
        }
        else
        {
            LOGWARN("No DNF for this function: " + FuncName);
            exit(-1);
        }
    }
}

bool CFGVisitor::DealWithStmt(Stmt *stmt, TransitionSystem &transystem, FunctionDecl *func)
{
    // DONE: Deal with assignment statement in code.
    // DONE: Deal with If statement in code.
    // DONE: Deal with For loop in code.
    // DONE: Deal with the situation of continue and break in code. [hint: consider the guard to break to be loop guard in break situation and the standalone branch cutted in continue statement]
    // DONE: Deal with the return statement in loop.
    PrintStmtInfo(stmt);
    if (isa<IfStmt>(stmt))
    {
        IfStmt *ifStmt = dyn_cast<IfStmt>(stmt);
        Expr *condition = ifStmt->getCond();
        Stmt *then_branch = ifStmt->getThen();
        Stmt *else_branch = ifStmt->getElse();
        vector<vector<Expr *>> RecIneqDNF = transystem.getIneqDNF();
        vector<ACSLComment *> rec_comments = transystem.getComments();
        TransitionSystem ElseTransystem(transystem);
        TransitionSystem ThenTransystem(transystem);
        ThenTransystem.MergeCond(PreprocessExpr(condition, ThenTransystem), false);
        ElseTransystem.MergeCond(NegateExpr(PreprocessExpr(condition, ElseTransystem)), false);
        if (then_branch)
            if (CompoundStmt *compound = dyn_cast<CompoundStmt>(then_branch))
            {
                for (auto stmt : compound->body())
                {
                    bool flag = DealWithStmt(stmt, ThenTransystem, func);
                    if (!flag)
                        break;
                }
            }
            else
            {
                DealWithStmt(then_branch, ThenTransystem, func);
            }
        if (else_branch)
            if (CompoundStmt *compound = dyn_cast<CompoundStmt>(else_branch))
            {
                for (auto stmt : compound->body())
                {
                    bool flag = DealWithStmt(stmt, ElseTransystem, func);
                    if (!flag)
                        break;
                }
            }
            else
            {
                DealWithStmt(else_branch, ElseTransystem, func);
            }
        transystem = TransitionSystem::MergeTransystem(ThenTransystem, ElseTransystem);
        transystem.MergeComments(rec_comments);
    }
    else if (isa<ForStmt>(stmt) || isa<WhileStmt>(stmt))
    {
        vector<vector<Expr *>> RemainDNF;
        bool flag;
        Expr *LoopCond;
        Stmt *LoopBody;
        SourceRange sourceRange;
        Expr *inc = NULL;
        if (isa<ForStmt>(stmt))
        {
            flag = true;
            ForStmt *forstmt = dyn_cast<ForStmt>(stmt);
            DealWithStmt(forstmt->getInit(), transystem, func);
            LoopCond = PreprocessExpr(forstmt->getCond(), transystem);
            LoopBody = forstmt->getBody();
            sourceRange = forstmt->getSourceRange();
            inc = forstmt->getInc();
        }
        else
        {
            flag = false;
            WhileStmt *whileStmt = dyn_cast<WhileStmt>(stmt);
            LoopCond = PreprocessExpr(whileStmt->getCond(), transystem);
            LoopBody = whileStmt->getBody();
            sourceRange = whileStmt->getSourceRange();
        }
        unordered_set<string> UsedVars;
        vector<vector<Expr *>> SkipLoop = transystem.DealwithCond(LoopCond, false);
        transystem.UpdateVars(true);
        SkipLoop = Merge_DNF(SkipLoop, AppendDNF(transystem.getDNF(), transystem.getIneqDNF()));
        transystem.MergeCond(LoopCond, true);
        vector<vector<Expr *>> InitDNF = transystem.getDNF();
        vector<vector<Expr *>> InitIneqDNF = transystem.getIneqDNF();
        vector<vector<VariableInfo>> InitVars = transystem.getVars();
        SourceLocation startLocation = sourceRange.getBegin();
        SourceManager &sourceManager = context->getSourceManager();
        int lineNumber = sourceManager.getSpellingLineNumber(startLocation);
        ACSLComment *LoopComment = new ACSLComment(lineNumber, ACSLComment::CommentType::LOOP);
        transystem.AddComment(LoopComment);
        transystem.InLoop();

        if (isa<ForStmt>(stmt))
        {
            ForStmt *forstmt = dyn_cast<ForStmt>(stmt);
            LoopCond = PreprocessExpr(forstmt->getCond(), transystem);
        }
        else
        {
            WhileStmt *whileStmt = dyn_cast<WhileStmt>(stmt);
            LoopCond = PreprocessExpr(whileStmt->getCond(), transystem);
        }
        transystem.MergeCond(LoopCond, true);
        LOGINFO("start loop");
        if (LoopBody)
        {
            if (CompoundStmt *compound = dyn_cast<CompoundStmt>(LoopBody))
            {
                for (auto stmt : compound->body())
                {
                    bool ContinueFlag = DealWithStmt(stmt, transystem, func);
                    if (!ContinueFlag)
                        break;
                }
                if (flag)
                    DealWithStmt(inc, transystem, func);
                transystem.ArrayInvariantProcess();
                transystem.UpdateVars(false);
                UsedVars = transystem.getUsedVars(LoopCond, inc);
            }
            else
            {
                DealWithStmt(LoopBody, transystem, func);
                transystem.ArrayInvariantProcess();
                transystem.UpdateVars(false);
            }
        }
        RemainDNF = transystem.OutLoop(LoopCond, UsedVars, InitDNF, InitIneqDNF, InitVars, LocalVars);
        transystem.ProcessSkipDNF(SkipLoop);
        PrintDNF(SkipLoop);
        transystem.AfterLoop(SkipLoop, UsedVars);
        LoopComment->add_invariant(SkipLoop, true);
        LoopComment->deduplication();
        LoopComment->add_invariant(RemainDNF, false);
        transystem.deduplicate(LoopComment->GetInv());
    }
    else if (isa<DoStmt>(stmt))
    {
        DoStmt *dostmt = dyn_cast<DoStmt>(stmt);
        Stmt *LoopBody = dostmt->getBody();
        if (LoopBody)
            if (CompoundStmt *compound = dyn_cast<CompoundStmt>(LoopBody))
            {
                for (auto stmt : compound->body())
                {
                    bool ContinueFlag = DealWithStmt(stmt, transystem, func);
                    if (!ContinueFlag)
                        break;
                }
            }
            else
            {
                DealWithStmt(LoopBody, transystem, func);
            }
        WhileStmt *newWhile = WhileStmt::CreateEmpty(*context, false);
        newWhile->setBody(LoopBody);
        newWhile->setCond(dostmt->getCond());
        newWhile->setWhileLoc(dostmt->getDoLoc());
        DealWithStmt(newWhile, transystem, func);
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
        UnaryOperator *unop = dyn_cast<UnaryOperator>(stmt);
        unop = dyn_cast<UnaryOperator>(unop);
        DealWithUnaryOp(unop, transystem);
    }
    else if (isa<ContinueStmt>(stmt))
    {
        return false;
    }
    else if (isa<BreakStmt>(stmt))
    {
        DeclRefExpr *breakflag = createDeclRefExpr("break");
        transystem.AddExpr(breakflag);
        return false;
    }
    else if (isa<CallExpr>(stmt))
    {
        CallExpr *call = dyn_cast<CallExpr>(stmt);
        string ReturnValue;
        DealWithCallExpr(call, transystem, ReturnValue);
    }
    else if (isa<ReturnStmt>(stmt))
    {
        // DONE: When Exit, record current DNF and RecIneqDNF (update var)
        ReturnStmt *ret = dyn_cast<ReturnStmt>(stmt);
        transystem.UpdateVars(false);
        vector<vector<Expr *>> ReturnDNF;
        string FuncName = func->getNameAsString();
        transystem.PrintDNF();
        transystem.PrintVars();
        ReturnDNF = AppendDNF(transystem.getIneqDNF(), transystem.getDNF());
        VerifiedFunc.insert(FuncName);
        string return_name = FuncName + "_RetVal";
        DeclRefExpr *returnExpr = createDeclRefExpr(return_name);
        Expr *returnValue = ret->getRetValue();
        returnValue = createBinOp(returnExpr, returnValue, BO_Assign);
        for (int i = 0; i < ReturnDNF.size(); i++)
        {
            ReturnDNF[i].push_back(returnValue);
        }
        FuncsDNF[FuncName] = ConnectDNF(FuncsDNF[FuncName], ReturnDNF);
        transystem.clear();
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
    ArrayIndex.clear();
    SourceManager &SM = context->getSourceManager();
    if (!SM.isInMainFile(func->getLocation()))
        return true;
    if (VS == VisitorState::Collect_All_Function)
    {
        MainFuncs.insert(func->getNameAsString());
        return true;
    }
    if (VerifiedFunc.count(func->getNameAsString()) != 0)
        return true;

    TransitionSystem transystem;
    transystem.init();
    LOGINFO("Current Function:" + func->getNameAsString());
    if (func->getNameAsString() == "main")
        for (auto name : global_vars)
        {
            IntegerLiteral *zero = createIntegerLiteral(0);
            DeclRefExpr *decl = createDeclRefExpr(name);
            BinaryOperator *binop = createBinOp(decl, zero, BO_Assign);
            transystem.AddExpr(binop);
        }
    Stmt *FuncBody = func->getBody();
    if (CompoundStmt *compound = dyn_cast<CompoundStmt>(FuncBody))
    {
        for (auto stmt : compound->body())
        {
            bool flag = DealWithStmt(stmt, transystem, func);
            if (!flag)
                break;
        }
    }
    else
        DealWithStmt(FuncBody, transystem, func);
    if (VerifiedFunc.find(func->getNameAsString()) == VerifiedFunc.end())
    {
        VerifiedFunc.insert(func->getNameAsString());
        transystem.UpdateVars(false);
        vector<vector<Expr *>> ReturnDNF;
        string FuncName = func->getNameAsString();
        ReturnDNF = AppendDNF(transystem.getIneqDNF(), transystem.getDNF());
        FuncsDNF[FuncName] = ConnectDNF(FuncsDNF[FuncName], ReturnDNF);
    }
    AddComments(transystem.getComments());
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

void CFGVisitor::AddComments(vector<ACSLComment *> RecComment)
{
    comments.insert(comments.end(), RecComment.begin(), RecComment.end());
    return;
}

void CFGVisitor::Dump_Annotated_file()
{
    int lineNumber = 0;
    string line;
    int index = 0;
    if (comments.size() == 0)
    {
        LOGWARN("No comments have been generated");
        exit(1);
    }
    int CurLineNo = comments[index]->getLineNum();
    while (getline(infile, line))
    {
        lineNumber++;
        while (lineNumber == CurLineNo)
        {
            comments[index]->dump(outfile, context);
            index++;
            if (index != comments.size())
            {
                CurLineNo = comments[index]->getLineNum();
            }
            else
            {
                CurLineNo = -1;
                break;
            }
        }
        outfile << line << "\n";
    }
    return;
}