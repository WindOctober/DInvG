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
    LoopCount = 0;
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

void CParser::ProcessProgramState(ProgramState* state) {
    if (state->IsInLoop()) {
        // TODO: Assign the transition condition to the corresponding loop body
        // (hence, a loop body identifier is needed), allowing the external
        // CParser to calculate the invariant for this LinTS once all conditions
        // of a loop have been collected.
    }
}
void CParser::TraverseProgramStmt(Stmt* stmt,
                                  ProgramState* curState,
                                  Stmt* nextStmt) {
    if (stmt == nullptr) {
        ProcessProgramState(curState);
        return;
    }
    if (isa<IfStmt>(stmt)) {
        IfStmt* ifstmt = dyn_cast<IfStmt>(stmt);
        Expr* cond = ifstmt->getCond();
        Stmt* thenBranch = ifstmt->getThen();
        if (ifstmt->hasElseStorage()) {
            Stmt* elseBranch = ifstmt->getElse();
            ProgramState* branchState(curState);

            TraverseProgramStmt(elseBranch, branchState, nextStmt);
            return;
        }
        TraverseProgramStmt(thenBranch, curState, nextStmt);
        return;
    } else if (isa<WhileStmt>(stmt)) {
        WhileStmt* whilestmt = dyn_cast<WhileStmt>(stmt);
        Stmt* whileBody = whilestmt->getBody();
        Expr* cond = whilestmt->getCond();
        if (curState->CheckInconsistentCond(cond)) {
            TraverseProgramStmt(nextStmt, curState, NULL);
            return;
        }
        // TODO: Here, it is necessary to clear the variable initialization
        // information in curState.
        ProgramState* inWhileState(curState);
        inWhileState->setIntoLoop(++LoopCount);
        inWhileState->addConstraint(cond);
        // TODO: Set the initial condition for the loop and the initial
        // condition for the corresponding LinTS. A function should be created
        // in the CParser class to handle this.
        TraverseProgramStmt(whileBody, inWhileState, NULL);
        // TODO: Once all conditions required for calculating the invariant of a
        // loop are collected, CParser should perform backend LinTS construction
        // and computation here, and use the calculated exit part of the
        // invariant to update the current state.
        TraverseProgramStmt(nextStmt, curState, NULL);
        return;
    } else if (isa<DoStmt>(stmt)) {
        DoStmt* dostmt = dyn_cast<DoStmt>(stmt);
        // TODO: The operation for DoStmt is to add the 'do' part on top of the
        // existing WhileStmt, which does not require excessive attention.
    } else if (isa<ForStmt>(stmt)) {
        ForStmt* forstmt = dyn_cast<ForStmt>(stmt);
        TraverseProgramStmt(forstmt->getInit(), curState, NULL);
        Expr* cond = forstmt->getCond();
        if (curState->CheckInconsistentCond(cond)) {
            TraverseProgramStmt(nextStmt, curState, NULL);
            return;
        }
        // TODO: The operation for ForStmt is to add the 'init' and 'inc' parts
        // on top of the existing WhileStmt, which does not require excessive
        // attention.
    } else if (isa<ContinueStmt>(stmt)) {
        ContinueStmt* continuestmt = dyn_cast<ContinueStmt>(stmt);
        TraverseProgramStmt(NULL, curState, NULL);
    } else if (isa<BreakStmt>(stmt)) {
        BreakStmt* breakstmt = dyn_cast<BreakStmt>(stmt);
        curState->setBreakFlag();
        TraverseProgramStmt(NULL, curState, NULL);
    } else if (isa<ReturnStmt>(stmt)) {
        ReturnStmt* returnstmt = dyn_cast<ReturnStmt>(stmt);
        delete curState;
        return;
    } else if (isa<CompoundStmt>(stmt)) {
        CompoundStmt* compound = dyn_cast<CompoundStmt>(stmt);
        SmallVector<Stmt*, 8> stmtList;
        Stmt* firstStmt = NULL;
        for (Stmt* stmt : compound->body()) {
            if (firstStmt == NULL)
                firstStmt = stmt;
            else
                stmtList.push_back(stmt);
        }
        stmtList.push_back(nextStmt);
        TraverseProgramStmt(firstStmt, curState, CreateCompoundStmt(stmtList));
        return;
    } else if (isa<DeclStmt>(stmt)) {
        DeclStmt* decl = dyn_cast<DeclStmt>(stmt);
        for (Decl* singleDecl : decl->getDeclGroup()) {
            if (isa<VarDecl>(singleDecl)) {
                VarDecl* singleVarDecl = dyn_cast<VarDecl>(singleDecl);
                string varName = singleVarDecl->getNameAsString();
                Expr* varInit = singleVarDecl->getInit();
                // TODO:Before an expression is integrated into the program
                // state, it must be ensured that it can be converted into a
                // linear expression form recognized by the PPL (Parma Polyhedra
                // Library). Therefore, a preprocessing function needs to be
                // introduced to preprocess each expression.
            } else {
                throw runtime_error(
                    "We currently do not support handling declarations other "
                    "than variable declarations inside functions (such as "
                    "defining another function within a function). This would "
                    "complicate the code analysis and introduce unnecessary "
                    "logic (for the time being).");
            }
        }
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