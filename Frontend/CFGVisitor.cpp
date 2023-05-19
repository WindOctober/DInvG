#include "CFGVisitor.hpp"
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
    }
    errs() << "CFGVisitor::Terminate_errors UnknownError";
    return;
}
void CFGVisitor::DealWithVarDecl(const VarDecl *stmt)
{
    if (stmt == NULL)
        Terminate_errors(ErrorType::VarDeclUnFoundError);
    // Deal with pointer, pure numeric, arrays.
    QualType stmt_type = stmt->getType();
    string var_name = stmt->getName();

    if (stmt_type->isArrayType())
    {

        return;
    }
    if (stmt_type->isPointerType())
    {
        QualType pointer_type = stmt_type->getPointeeType();
        if (pointer_type->isFloatingType())
            Terminate_errors(ErrorType::FloatVarError);

        return;
    }
    if (stmt_type->isIntegerType())
    {
        outs() << stmt_type.getAsString() << "\n";
        outs() << var_name << "\n";
        const Expr *init = stmt->getInit();

        return;
    }
    if (stmt_type->isFloatingType())
        Terminate_errors(ErrorType::FloatVarError);
}

void CFGVisitor::DealWithFunctionDecl(const FunctionDecl *stmt)
{
}
void CFGVisitor::DealWithStmt(const Stmt *stmt)
{
    // Deal with the whole Stmt in code. (which usually means the complete statement in one line.)
    // string stmt_type=stmt->getStmtClassName();
    // string stmt_str;
    // raw_string_ostream ostream(stmt_str);
    // stmt->printPretty(ostream,nullptr,pp);
    // ostream.flush();
    // outs()<<stmt_str<<"\n";
    if (isa<IfStmt>(stmt)){

    }
    else if (isa<WhileStmt>(stmt)){
        
    }
    else if (isa<DeclStmt>(stmt))
    {
        const DeclStmt *declStmt = dyn_cast<DeclStmt>(stmt);
        for (const auto *decl : declStmt->decls())
        {
            if (isa<VarDecl>(decl))
            {
                DealWithVarDecl(dyn_cast<VarDecl>(decl));
            }
            else if (isa<FunctionDecl>(decl))
            {
                DealWithFunctionDecl(dyn_cast<FunctionDecl>(decl));
            }
            else if (isa<FieldDecl>(decl))
            {
                // Add your code to deal with FieldDecl here
            }
        }
        return;
    }
    else if (isa<BinaryOperator>(stmt))
    {
    }

    return;
}


bool CFGVisitor::VisitCallExpr(CallExpr *CE)
{
    if (VS != VisitorState::Main)
        return true;
    FunctionDecl *callee = CE->getDirectCallee();
    if (callee && Visited_Functions.count(callee->getNameAsString()) == 0)
    {
        SourceManager &SM = context->getSourceManager();
        if (!SM.isInMainFile(callee->getLocation()))
            return true;
        Visited_Functions.insert(callee->getNameAsString());
        auto cfg = CFG::buildCFG(callee, callee->getBody(), context, CFG::BuildOptions());
        outs() << "CalleeFunction:" << callee->getNameAsString() << "\n";
        // TraverseCFG(cfg);
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
        Stmt* func_body=func->getBody();
        if (CompoundStmt* compound=dyn_cast<CompoundStmt>(func_body)){
            for (auto stmt : compound->body()){
                outs()<<stmt->getStmtClassName()<<'\n';
            }
        }
    }
    return true;
}