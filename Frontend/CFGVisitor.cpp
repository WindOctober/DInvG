// TODO: alter the source code and generate a annotated version (with invariant annotations before the while loop)
// TODO: think how to solve the inter-procedural invariant.
#include "CFGVisitor.hpp"
#include "TransitionSystem.hpp"
#include "Library.hpp"
#include <iostream>
#include <memory>

set<string> Main_Functions;
set<string> Visited_Functions;

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
void CFGVisitor::DealWithVarDecl(VarDecl *stmt, TransitionSystem &transystem)
{
    VariableInfo var;
    if (stmt == NULL)
        Terminate_errors(ErrorType::VarDeclUnFoundError);
    // Deal with pointer, pure numeric, arrays.
    QualType stmt_type = stmt->getType();
    string var_name = stmt->getName();
    if (stmt_type->isArrayType())
    {
    }
    else if (stmt_type->isPointerType())
    {
        QualType pointer_type = stmt_type->getPointeeType();
        if (pointer_type->isFloatingType())
            Terminate_errors(ErrorType::FloatVarError);
    }
    else if (stmt_type->isIntegerType())
    {
        var.alterVar(var_name, stmt->getInit(), stmt_type, transystem.get_InLoop());
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
        var.alterVar(stmt->getLHS(), NULL, transystem.get_InLoop());
        transystem.add_vars(var, stmt->getRHS());
    }
    return;
}

void CFGVisitor::DealWithFunctionDecl(FunctionDecl *stmt, TransitionSystem &transystem)
{
}
void CFGVisitor::DealWithStmt(Stmt *stmt, TransitionSystem &transystem)
{
    // Deal with the whole Stmt in code. (which usually means the complete statement in one line.)

    // DONE: Deal with assignment statement in code.
    // TODO: Deal with If statement in code.
    // TODO: Deal with For loop in code.
    // TODO: Deal with the situation of continue and break in code. [hint: consider the guard to break to be loop guard in break situation and the standalone branch cutted in continue statement]
    // TODO: Deal with special cases likes x=(a==b), y=(a>=b), which should be handled to if (a==b) x=1 else x=0 and so on.
    PrintStmtInfo(stmt);
    if (transystem.get_Canonical_count() == 0)
    {
        transystem.init_Canonical(1);
    }
    if (isa<IfStmt>(stmt))
    {
        IfStmt *ifStmt = dyn_cast<IfStmt>(stmt);
        Expr *condition = ifStmt->getCond();
        Stmt *then_branch = ifStmt->getThen();
        Stmt *else_branch = ifStmt->getElse();
        TransitionSystem ElseTransystem(transystem);
        TransitionSystem ThenTransystem(transystem);
        ThenTransystem.Merge_condition(condition, false);
        ElseTransystem.Merge_condition(transystem.NegateExpr(condition), false);
        if (CompoundStmt *compound = dyn_cast<CompoundStmt>(then_branch))
        {
            for (auto stmt : compound->body())
            {
                DealWithStmt(stmt, ThenTransystem);
            }
        }
        if (CompoundStmt *compound = dyn_cast<CompoundStmt>(else_branch))
        {
            for (auto stmt : compound->body())
            {
                DealWithStmt(stmt, ElseTransystem);
            }
        }
        transystem = TransitionSystem::Merge_Transystem(ThenTransystem, ElseTransystem);
    }
    else if (isa<ForStmt>(stmt))
    {
        // TODO: Process if For loop body is empty;
    }
    else if (isa<WhileStmt>(stmt))
    {
        // DONE: Before Into loop -> get precondition from Vars vector.
        // TODO: Process if While loop body is empty.
        WhileStmt *whileStmt = dyn_cast<WhileStmt>(stmt);
        SourceRange sourceRange = whileStmt->getSourceRange();
        SourceLocation startLocation = sourceRange.getBegin();
        SourceManager &sourceManager =context->getSourceManager();
        int lineNumber = sourceManager.getSpellingLineNumber(startLocation);
        ACSLComment *loop_comment=new ACSLComment(lineNumber,ACSLComment::CommentType::LOOP);
        
        Expr *loop_condition = whileStmt->getCond();
        loop_comment->add_invariant(transystem.Deal_with_condition(loop_condition,false));
        transystem.add_comment(loop_comment);
        Stmt *while_body = whileStmt->getBody();
        transystem.Merge_condition(loop_condition, false);
        transystem.In_Loop();
        if (CompoundStmt *compound = dyn_cast<CompoundStmt>(while_body))
        {
            for (auto stmt : compound->body())
            {
                DealWithStmt(stmt, transystem);
            }
            transystem.Update_Loop_Vars();
        }
        transystem.Out_Loop(whileStmt);
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
    return;
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
    if (func->getNameAsString() == "main" || Main_Functions.count("main") == 0)
    {
        TransitionSystem transystem;
        Stmt *func_body = func->getBody();
        if (CompoundStmt *compound = dyn_cast<CompoundStmt>(func_body))
        {
            for (auto stmt : compound->body())
            {
                DealWithStmt(stmt, transystem);
            }
        }
    }
    return true;
}

void CFGVisitor::PrintStmtInfo(Stmt *stmt)
{
    // TODO: complete this function case by case
    outs() << "\n\n";
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