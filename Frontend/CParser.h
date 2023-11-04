#include <clang/Frontend/CompilerInstance.h>

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
    enum class ParserState{
        PREPROCESS,
        PARSING
    };
    CParser(clang::ASTContext* context,ParserState pState);
    bool VisitFunctionDecl(clang::FunctionDecl *funcDecl);

private:
    void TraverseProgramStmt(clang::Stmt* stmt, ProgramState* curState,clang::Stmt* nextStmt);
    ParserState pState;
    
};