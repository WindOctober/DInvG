#ifndef INV_TRANSITIONSYSTEM
#define INV_TRANSITIONSYSTEM
#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Analysis/CFG.h"
#include "Variable.hpp"
#include <vector>
#include <ppl.hh>
#include <string>

using namespace std;
using namespace clang;
using namespace llvm;

class TransitionSystem
{
public:
    // TODO: process the transformation from the Expr* to Constraint*.
    // TODO: process the generation of the Locations and Transitions.

    void Compute_Loop_Invariant();

    void init_Canonical(int size);
    TransitionSystem(ASTContext *&astcontext);
    int get_Canonical_count();
    bool get_InLoop();

    void Merge_condition(Expr *condition);
    void Split_If();

    void In_Loop();
    Expr *Trans_VariableInfo_to_Expr(VariableInfo var);
    Expr *Trans_VariableInfo_to_InitExpr(VariableInfo var);
    Constraint *Trans_Expr_to_Constraint(Expr *expr);
    vector<vector<Expr *>> Deal_with_condition(Expr *condition, bool not_logic, vector<vector<Expr *>> cur);
    vector<vector<Expr *>> Merge_DNF(vector<vector<Expr *>> left_expr, vector<vector<Expr *>> right_expr);
    vector<vector<Expr *>> Connect_DNF(vector<vector<Expr *>> left_expr, vector<vector<Expr *>> right_expr);
    void Update_Init_Vars();
    void Update_Loop_Vars();
    void copy_after_update(int size);
    void Out_Loop(WhileStmt *whileloop);

    void Print_Vars();
    void Print_DNF();

    void add_vars(VariableInfo var);
    void add_expr(Expr *expr);

private:
    ASTContext *context;
    vector<vector<VariableInfo>> Vars;
    int Verified_Loop_Count;
    vector<vector<Expr *>> DNF;
    vector<vector<Expr *>> Init_DNF;
    int Canonical_Branch_Count;
    bool InWhileLoop;
    int Inner_Loop_Depth;
    int Inner_Loop_Count;
};

#endif