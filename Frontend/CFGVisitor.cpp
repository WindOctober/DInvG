// TODO: alter the source code and generate a annotated version (with invariant annotations before the while loop)
// TODO: think how to solve the inter-procedural invariant.
#include "CFGVisitor.hpp"
#include "TransitionSystem.hpp"
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
void CFGVisitor::DealWithVarDecl(VarDecl *stmt, int left, int right)
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
        var.alterVar(var_name, stmt->getInit(), stmt_type);
    }
    else if (stmt_type->isFloatingType())
        Terminate_errors(ErrorType::FloatVarError);
    Transystem.add_vars(var, left, right);
}

void CFGVisitor::DealWithUnaryOp(UnaryOperator *stmt, int left, int right)
{
    Expr *res;
    Expr *left_value = stmt->getSubExpr();
    FPOptions default_options;
    if (stmt->getOpcode() == UO_PreDec || stmt->getOpcode() == UO_PostDec)
    {
        IntegerLiteral *one = IntegerLiteral::Create(*context, APInt(32, 1), context->IntTy, SourceLocation());
        BinaryOperator *plusOne = new (context) BinaryOperator(left_value, one, BO_Add, left_value->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
        res = new (*context) BinaryOperator(left_value, plusOne, BO_Assign, left_value->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
    }
    else if (stmt->getOpcode() == UO_PreInc || stmt->getOpcode() == UO_PostInc)
    {
        IntegerLiteral *one = IntegerLiteral::Create(*context, APInt(32, 1), context->IntTy, SourceLocation());
        BinaryOperator *minusOne = new (context) BinaryOperator(left_value, one, BO_Sub, left_value->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
        res = new (*context) BinaryOperator(left_value, minusOne, BO_Assign, left_value->getType(), VK_RValue, OK_Ordinary, SourceLocation(), default_options);
    }
    Transystem.add_expr(res, left, right);
    return;
}

void CFGVisitor::DealWithBinaryOp(BinaryOperator *stmt, int left, int right)
{
}

void CFGVisitor::DealWithFunctionDecl(FunctionDecl *stmt, int left, int right)
{
}
void CFGVisitor::DealWithStmt(Stmt *stmt, int left, int right)
{
    // Deal with the whole Stmt in code. (which usually means the complete statement in one line.)

    // TODO: Deal with assignment statement in code.
    // TODO: Deal with If statement in code.
    // TODO: Deal with For loop in code.
    PrintStmtInfo(stmt);
    if (Transystem.get_Canonical_count() == 0)
    {
        Transystem.init_Canonical(1);
        right=0;
    }
    if (isa<IfStmt>(stmt))
    {
    }
    else if (isa<ForStmt>(stmt))
    {
        // TODO: Process if For loop body is empty;
    }
    else if (isa<WhileStmt>(stmt))
    {
        // TODO: Before Into loop -> get precondition from Vars vector.
        // TODO: Process if While loop body is empty.
        WhileStmt *whileStmt = dyn_cast<WhileStmt>(stmt);
        Expr *loop_condition = whileStmt->getCond();
        Stmt *while_body = whileStmt->getBody();
        Transystem.In_Loop(loop_condition);
        if (CompoundStmt *compound = dyn_cast<CompoundStmt>(while_body))
        {
            for (auto stmt : compound->body())
            {
                DealWithStmt(stmt, left, right);
            }
            Transystem.Print_DNF();
        }
    }
    else if (isa<DeclStmt>(stmt))
    {
        DeclStmt *declStmt = dyn_cast<DeclStmt>(stmt);
        
        for (auto *decl : declStmt->decls())
        {
            if (isa<VarDecl>(decl))
            {
                DealWithVarDecl(dyn_cast<VarDecl>(decl), left, right);
            }
            else if (isa<FunctionDecl>(decl))
            {
                DealWithFunctionDecl(dyn_cast<FunctionDecl>(decl), left, right);
            }
        }
    }
    else if (isa<BinaryOperator>(stmt))
    {

        BinaryOperator *binop = dyn_cast<BinaryOperator>(stmt);

    }
    else if (isa<ParenExpr>(stmt))
    {
        ParenExpr *expr = dyn_cast<ParenExpr>(stmt);

    }
    else if (isa<UnaryOperator>(stmt))
    {
        UnaryOperator *unop = dyn_cast<UnaryOperator>(stmt);
        DealWithUnaryOp(unop, left, right);
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
        Stmt *func_body = func->getBody();
        if (CompoundStmt *compound = dyn_cast<CompoundStmt>(func_body))
        {
            for (auto stmt : compound->body())
            {
                DealWithStmt(stmt, 0, Transystem.get_Canonical_count() - 1);
            }
        }
    }
    return true;
}

void CFGVisitor::PrintStmtInfo(Stmt *stmt)
{
    // complete this function case by case
    outs()<<"\n\n";
    outs() << "[print statement info]"<<'\n';
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