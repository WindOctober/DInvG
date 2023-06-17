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

enum TransformationType
{
    Loc,
    Trans,
    Guard,
    Primed,
    Origin
};


void Log(const string &level, const string &function, int line, string msg);
string Print_Expr(Expr *expr);

vector<vector<Expr *>> Merge_DNF(vector<vector<Expr *>> left_expr, vector<vector<Expr *>> right_expr);
vector<vector<Expr *>> Connect_DNF(vector<vector<Expr *>> left_expr, vector<vector<Expr *>> right_expr);
vector<C_Polyhedron> Merge_Poly(vector<C_Polyhedron> &left_poly, vector<C_Polyhedron> &right_poly);

// vector<vector<vector<string>>> Derive_Vars_From_Poly(vector<C_Polyhedron> &poly, vector<VariableInfo> &vars);
Linear_Expression *Trans_Expr_to_LinExpr(Expr *expr, enum TransformationType type, int var_size);
Constraint_System *Trans_Expr_to_Constraints(Expr *expr, enum TransformationType type, int var_size);
vector<vector<Expr *>> Trans_Polys_to_Exprs(vector<C_Polyhedron> poly);
Expr *Trans_Constraint_to_Expr(Constraint constraint);

void Traverse_Expr_ForVars(Expr *expr,unordered_set<string> &res);
bool Traverse_Expr_CheckVars(Expr *expr,const unordered_set<string> &res);
bool check_guard(Expr *expr);

vector<C_Polyhedron> Compute_and_Eliminate_Init_Poly(const unordered_set<string>& used_vars, Expr *condition,vector<vector<Expr*>>& init_DNF,vector<vector<Expr*> > &init_ineq_DNF);
#endif