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
#include "ppl.hh"
#include <unordered_set>
using namespace std;
using namespace clang;
using namespace llvm;
#define INITSUFFIX "_initvariable_avoid_conflict"
#define PRIMESUFFIX "_primedvariable_avoid_conflict"
#define LOG_INFO(msg) Log("INFO", __FUNCTION__, __LINE__, msg)
#define LOG_WARNING(msg) Log("WARNING", __FUNCTION__, __LINE__, msg)

void Log(const string &level, const string &function, int line, string msg);
vector<vector<Expr *>> Merge_DNF(vector<vector<Expr *>> left_expr, vector<vector<Expr *>> right_expr);
vector<vector<Expr *>> Append_DNF(vector<vector<Expr *>> left_expr, vector<vector<Expr *>> right_expr);
vector<vector<Expr *>> Connect_DNF(vector<vector<Expr *>> left_expr, vector<vector<Expr *>> right_expr);
vector<C_Polyhedron> Merge_Poly(vector<C_Polyhedron> &left_poly, vector<C_Polyhedron> &right_poly);

#endif