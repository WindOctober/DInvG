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
#include <unordered_set>

using namespace std;
using namespace clang;
using namespace llvm;

class TransitionSystem
{
public:
    // DONE: process the transformation from the Expr* to Constraint*.
    // DONE: process the generation of the Locations and Transitions.
    // TODO: process the merge of two transition system while split by if statement.
    // TODO: 
    enum class TransformationType
    {
        Location,
        Transition,
        Guard,
        Primed,
        Origin
    };
    void Compute_Loop_Invariant(Expr* condition);
    vector<C_Polyhedron *> Compute_and_Eliminate_Init_Poly(vector<VariableInfo> used_vars);
    void Elimiate_Impossible_Path(int size);
    void Initialize_Locations_and_Transitions(int locsize, int varsize,Expr* condition);

    void init_Canonical(int size);
    TransitionSystem(ASTContext *&astcontext);
    TransitionSystem(TransitionSystem& other);
    int get_Canonical_count();
    bool get_InLoop();
    vector<VariableInfo> get_Used_Vars();

    void Traverse_Expr_ForVars(Expr *expr, unordered_set<VariableInfo> &res);
    void Merge_condition(Expr *condition);
    void Split_If();
    Expr* NegateExpr(Expr* expr);

    void In_Loop();
    Expr *Trans_VariableInfo_to_Expr(VariableInfo var);
    Expr *Trans_VariableInfo_to_InitExpr(VariableInfo var);
    Constraint_System *Trans_Expr_to_Constraints(Expr *expr, enum TransformationType type, int var_size);
    Linear_Expression *Trans_Expr_to_LinExpr(Expr *expr, enum TransformationType type, int var_size);
    vector<vector<Expr *>> Deal_with_condition(Expr *condition, bool not_logic, vector<vector<Expr *>> cur);
    vector<vector<Expr *>> Merge_DNF(vector<vector<Expr *>> left_expr, vector<vector<Expr *>> right_expr);
    vector<vector<Expr *>> Connect_DNF(vector<vector<Expr *>> left_expr, vector<vector<Expr *>> right_expr);
    void Update_Init_Vars();
    void Update_Loop_Vars();
    void copy_after_update(int size);
    void Out_Loop(WhileStmt *whileloop);

    string Print_Expr(Expr *expr);
    void Print_Vars();
    void Print_DNF();

    void add_vars(VariableInfo var);
    void add_expr(Expr *expr);
    bool check_guard(Expr *expr);

private:
    int Verified_Loop_Count;

    ASTContext *context;
    vector<vector<VariableInfo>> Init_Vars;
    vector<vector<VariableInfo>> Vars;
    vector<vector<Expr *>> DNF;
    vector<vector<Expr *>> Init_DNF;
    int Canonical_Branch_Count;
    int Init_Branch_Count;

    bool InWhileLoop;
    int Inner_Loop_Depth;
    int Inner_Loop_Count;
};

#endif