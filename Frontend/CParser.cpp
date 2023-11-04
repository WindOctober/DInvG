#include "CParser.h"
#include <stdexcept>

using namespace std;
using namespace llvm;
using namespace clang;

extern ASTContext* globalContext;

CParser::CParser(ASTContext* context, ParserState state) {
    if (pselect == nullptr)
        pState = state;
    globalContext = context;
    return;
}

// The parser begins with the entry into the VisitFunctionDecl function, which
// then confirms the main function. Within the main function, it analyzes the
// required System and invokes backend tools for solving.
bool CParser::VisitFunctionDecl(FunctionDecl* funcDecl) {
    if (pState == ParserState::PREPROCESS) {
        return true;
    }
    if (!funcDecl->hasBody())
        return true;
    SourceManager& manager = globalContext->getSourceManager();
    if (!manager.isInMainFile(funcDecl->getLocation()))
        return true;
    string funcName = funcDecl->getNameAsString();
    if (funcName != "main")
        return true;
    Stmt* funcBody = funcDecl->getBody();
    if (!isa<CompoundStmt>(funcBody)) {
        throw runtime_error(
            "The body of the function is not a compound statement?");
    }
    ProgramState* proState = new ProgramState();
    TraverseProgramStmt(funcBody, proState, NULL);
    return false;
}

// This function deals with the impact of each specific statement on the current
// program state, as well as the potential influence on the overall LinTS.

// NOTE: We mainly handle the following statements: IfStmt, WhileStmt, DoStmt,
// ForStmt, ContinueStmt, BreakStmt, ReturnStmt, CompoundStmt, DeclStmt,
// BinaryOperator, CallExpr.
void CParser::TraverseProgramStmt(Stmt* stmt, ProgramState* curState, Stmt* nextStmt) {
    if (stmt == nullptr)
        return;
    if (isa<IfStmt>(stmt)) {
        IfStmt* ifstmt = dyn_cast<IfStmt>(stmt);
        Expr* cond=ifstmt->getCond();
        Stmt* thenBranch=ifstmt->getThen();
        if (ifstmt->hasElseStorage()){
            Stmt* elseBranch=ifstmt->getElse();
            ProgramState* branchState(curState);

            TraverseProgramStmt(elseBranch,branchState,nextStmt);
            return;
        }
        TraverseProgramStmt(thenBranch,curState,nextStmt);
        return;
    } else if (isa<WhileStmt>(stmt)) {
        WhileStmt* whilestmt = dyn_cast<WhileStmt>(stmt);
        Stmt* whileBody=whilestmt->getBody();
        Expr* cond=whilestmt->getCond();
        if (curState->inconsistentCond(cond)){
            TraverseProgramStmt(nextStmt,curState,NULL);
            return;
        }
        curState->addConstraint(cond);
        TraverseProgramStmt(whileBody,curState,NULL);
        

    } else if (isa<DoStmt>(stmt)) {
        DoStmt* dostmt = dyn_cast<DoStmt>(stmt);
    } else if (isa<ForStmt>(stmt)) {
        ForStmt* forstmt = dyn_cast<ForStmt>(stmt);
    } else if (isa<ContinueStmt>(stmt)) {
        ContinueStmt* continuestmt = dyn_cast<ContinueStmt>(stmt);
    } else if (isa<BreakStmt>(stmt)) {
        BreakStmt* breakstmt = dyn_cast<BreakStmt>(stmt);
    } else if (isa<ReturnStmt>(stmt)) {
        ReturnStmt* returnstmt = dyn_cast<ReturnStmt>(stmt);
    } else if (isa<CompoundStmt>(stmt)) {
        CompoundStmt* compound = dyn_cast<CompoundStmt>(stmt);
    } else if (isa<DeclStmt>(stmt)) {
        DeclStmt* decl = dyn_cast<DeclStmt>(stmt);
    } else if (isa<BinaryOperator>(stmt)) {
        BinaryOperator* binary = dyn_cast<BinaryOperator>(stmt);
    } else if (isa<CallExpr>(stmt)) {
        CallExpr* call = dyn_cast<CallExpr>(stmt);
    }
    throw runtime_error(
        "The current Stmt type being processed exceeds the predefined range of "
        "Stmt types.");
    return;
}