#ifndef INV_DEFINE
#define INV_DEFINE
#include <string>
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Analysis/CFG.h"
using namespace std;
using namespace clang;
using namespace llvm;
using namespace clang::tooling;
#define INITSUFFIX "_initvariable_avoid_var_conflict_october"
#define PRIMESUFFIX "_primedvariable_avoid_var_conflict_october"
#define LOG_INFO(msg) Log("INFO", __FUNCTION__, __LINE__, msg)
#define LOG_WARNING(msg) Log("WARNING", __FUNCTION__, __LINE__, msg)

void Log(const string& level, const string& function, int line,string msg);
string Print_Expr(Expr *expr);
#endif