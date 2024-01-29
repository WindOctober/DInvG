#ifndef CPARSER_H_
#define CPARSER_H_
#include <clang/Frontend/CompilerInstance.h>

#include "LinTS.h"
#include "ParserUtility.h"
#include "ProgramState.h"
extern clang::ASTContext* globalContext;
// NOTE: This parser by default analyzes the reachability properties within the
// program and assumes that SV-COMP-related functions in the program have
// certain predefined semantics. For instance, it defaults to the assumption
// that if an assert fails, reach_error() will be reached, and it allows
// reach_error() to be directly used in the program.

// NOTE: The parser may not handle inter-process operations with sufficient
// precision, especially with recursive functions involving the analysis of
// invariants among them. Currently, the parser's approach is relatively
// simplistic, thus it may require further optimization.
class CParser : public clang::RecursiveASTVisitor<CParser> {
   public:
    enum class ParserState { PREPROCESS, PARSING };
    CParser(clang::ASTContext* context, ParserState pState);
    bool VisitFunctionDecl(clang::FunctionDecl* funcDecl);

   private:
    clang::Expr* ProcessSpecialFunction(std::string funcName,
                                        clang::CallExpr* call,
                                        ProgramState* state);
    void ProcessProgramState(ProgramState* state);
    void TraverseProgramStmt(clang::Stmt* stmt,
                             ProgramState* curState,
                             clang::Stmt* nextStmt,
                             bool processing);
    clang::Expr* PreProcessExpr(clang::Expr* expr, ProgramState* state);
    void setLinTSInit(
        int index,
        std::vector<Parma_Polyhedra_Library::C_Polyhedron*> initPolys);
    void ComputeLinTSInv(int index, ProgramState* curState);
    ParserState pState;
    int LoopCount;
    int globalLocCount;
    std::map<int, std::vector<Parma_Polyhedra_Library::C_Polyhedron*>>
        linTSInit;
    std::map<int,
             std::map<int, std::vector<Parma_Polyhedra_Library::C_Polyhedron*>>>
        linTSLocConstrants;
    std::map<int, std::map<int, std::vector<bool>>> linTSLocNondetFlags;
    std::map<int, std::map<int, Parma_Polyhedra_Library::C_Polyhedron*>>
        linTSLocEqualities;
    std::map<int,
             std::map<int, std::vector<Parma_Polyhedra_Library::C_Polyhedron*>>>
        linTSAssertion;
    std::map<int, clang::Stmt*> IncStmts;
    std::map<int, std::unordered_set<int>> LinTSBreakLoc;
    std::map<int, LinTS*> linTSMap;
    std::map<int, std::vector<Parma_Polyhedra_Library::C_Polyhedron*>>
        loopExitCond;
    std::map<int, std::vector<bool>> loopExitFlags;
    std::map<int, std::map<int, int>> LocIdMap;
    enum LinTS::VERIFIEDRESULT finalRes;
};
#endif