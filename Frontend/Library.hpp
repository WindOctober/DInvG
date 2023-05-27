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
#include "Variable.hpp"
#include "TransitionSystem.hpp"
using namespace std;
using namespace clang;
using namespace llvm;
using namespace clang::tooling;
#define INITSUFFIX "_initvariable_avoid_var_conflict_october"
#define PRIMESUFFIX "_primedvariable_avoid_var_conflict_october"
#define LOG_INFO(msg) Log("INFO", __FUNCTION__, __LINE__, msg)
#define LOG_WARNING(msg) Log("WARNING", __FUNCTION__, __LINE__, msg)

void Log(const string &level, const string &function, int line, string msg);
string Print_Expr(Expr *expr);

vector<vector<Expr *>> Merge_DNF(vector<vector<Expr *>> left_expr, vector<vector<Expr *>> right_expr);
vector<vector<Expr *>> Connect_DNF(vector<vector<Expr *>> left_expr, vector<vector<Expr *>> right_expr);

vector<C_Polyhedron> Merge_Poly(vector<C_Polyhedron> &left_poly, vector<C_Polyhedron> &right_poly);
// vector<vector<vector<string>>> Derive_Vars_From_Poly(vector<C_Polyhedron> &poly, vector<VariableInfo> &vars);
Linear_Expression *Trans_Expr_to_LinExpr(Expr *expr, enum TransitionSystem::TransformationType type, int var_size);
Expr *Trans_Constraint_to_Expr(Constraint constraint);
vector<vector<Expr *>> Trans_Polys_to_Exprs(vector<C_Polyhedron> poly);
#endif