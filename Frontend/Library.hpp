#ifndef INV_DEFINE
#define INV_DEFINE
#include <string>
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "ppl.hh"
#include <unordered_set>
using namespace std;
using namespace clang;
using namespace llvm;
#define INITSUFFIX "_initvariable_avoid_conflict"
#define INDEXPREFIX "GlobalIndex"
#define PRIMESUFFIX "_primedvariable_avoid_conflict"
#define LOGINFO(msg) Log("INFO", __FUNCTION__, __LINE__, msg)
#define LOGWARN(msg) Log("WARNING", __FUNCTION__, __LINE__, msg)

extern int GlobalIndexCount;
extern ASTContext *astcontext;
void Log(const string &level, const string &function, int line, string msg);
string MakeIndexName();
vector<vector<Expr *>> Merge_DNF(vector<vector<Expr *>> left_expr, vector<vector<Expr *>> right_expr);
vector<vector<Expr *>> AppendDNF(vector<vector<Expr *>> left_expr, vector<vector<Expr *>> right_expr);
vector<vector<Expr *>> ConnectDNF(vector<vector<Expr *>> left_expr, vector<vector<Expr *>> right_expr);
vector<C_Polyhedron> Merge_Poly(vector<C_Polyhedron> &left_poly, vector<C_Polyhedron> &right_poly);

#endif