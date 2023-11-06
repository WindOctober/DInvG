#include "ParserUtility.h"

using namespace std;
using namespace clang;
using namespace llvm;

ASTContext* globalContext=nullptr;

CompoundStmt* CreateCompoundStmt(SmallVector<Stmt*,8> stmtList){
    CompoundStmt* compound=CompoundStmt::Create(*globalContext,stmtList,SourceLocation(),SourceLocation());
    return compound;
}