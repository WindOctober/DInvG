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
#include "ACSLComment.hpp"
#include <unordered_map>
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

    void Compute_Loop_Invariant(Expr *condition, unordered_set<string> vars_in_dnf, vector<C_Polyhedron> init_polys);

    void Elimiate_Impossible_Path(int size);
    void Initialize_Locations_and_Transitions(int locsize, int varsize, Expr *condition);

    void init_Canonical(int size);
    TransitionSystem();
    TransitionSystem(TransitionSystem &other);

    vector<ACSLComment *> get_Comments() { return comments; }
    unordered_set<string> get_Used_Vars();
    vector<vector<Expr *>> get_DNF() { return DNF; }
    ACSLComment* get_CurComment() {return comments[comments.size() - 1];}
    bool get_InLoop();

    void Merge_condition(Expr *condition, bool init_flag);
    void Split_If();
    static Expr *NegateExpr(Expr *expr);

    void set_incremental(Expr *increment); // only for for-loop, which is needed by continue situations.

    void In_Loop();
    Expr *Trans_Expr_by_CurVars(Expr *expr, vector<VariableInfo> &Vars);
    Expr *Trans_VariableInfo_to_Expr(VariableInfo var);

    vector<vector<Expr *>> Deal_with_condition(Expr *condition, bool not_logic);

    void Update_Vars();
    void copy_after_update(int size);
    void Out_Loop(WhileStmt *whileloop, unordered_set<string> used_vars, vector<vector<Expr *>> init_DNF);

    static TransitionSystem Merge_Transystem(TransitionSystem &left_trans, TransitionSystem &right_trans);

    void Print_Vars();
    void Print_DNF();

    void add_vars(VariableInfo &var);
    void add_vars(VariableInfo &var, Expr *expr);
    void add_expr(Expr *expr);
    void add_comment(ACSLComment *comment);

    static ASTContext *context;

private:
    vector<vector<Expr *>> Deal_with_condition(Expr *condition, bool not_logic, vector<vector<Expr *>> cur);

    int Verified_Loop_Count;
    vector<ACSLComment *> comments;
    vector<vector<Expr *>> inequality_DNF;
    vector<vector<VariableInfo>> Vars;
    vector<vector<Expr *>> DNF;

    bool InWhileLoop;
    int Inner_Loop_Depth;
    int Inner_Loop_Count;
};

#endif