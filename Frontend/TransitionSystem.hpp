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

enum TransformationType
{
    Loc,
    Trans,
    Guard,
    Primed,
    Origin
};

struct VarGraph{
    map<string,unordered_set<string>> edges;
    map<string,unordered_set<string>> possible_rv;  
};

class TransitionSystem
{
public:
    // DONE: process the transformation from the Expr* to Constraint*.
    // DONE: process the generation of the Locations and Transitions.
    // DONE: process the merge of two transition system while split by if statement.
    
    void Compute_Loop_Invariant(Expr *condition, unordered_set<string> vars_in_dnf, vector<C_Polyhedron> init_polys);

    void Elimiate_Impossible_Path(int size);
    void Initialize_Locations_and_Transitions(int locsize, int varsize, Expr *condition);

    void init_Canonical(int size);
    TransitionSystem();
    TransitionSystem(TransitionSystem &other);
    void Process_SkipDNF(vector<vector<Expr *>> &dnf);
    // void Construct_Graph();
    void After_loop(vector<vector<Expr *>> &dnf, unordered_set<string> &used_vars);

    void clear_ineqDNF() { inequality_DNF.clear(); }
    
    vector<vector<Expr *>> get_DNF() { return DNF; }
    int get_verified_loop() {return Verified_Loop_Count;}
    vector<vector<VariableInfo>> get_Vars() { return Vars; }
    vector<ACSLComment *> get_Comments() { return comments; }
    vector<vector<Expr *>> get_IneqDNF() { return inequality_DNF; }
    unordered_set<string> get_Used_Vars(Expr *cond, Expr *increment);
    ACSLComment *get_CurComment() { return comments[comments.size() - 1]; }
    

    static TransitionSystem Merge_Transystem(TransitionSystem &left_trans, TransitionSystem &right_trans);
    void Merge_condition(Expr *condition, bool updated);
    void Merge_IneqDNF(vector<vector<Expr *>> &dnf);
    void Merge_Comments(vector<ACSLComment *> &comment);
    void Merge_Function_Call(vector<vector<Expr*>> &function_dnf,FunctionDecl* func,string new_return_name);
    void Split_If();

    void init();
    void In_Loop();
    Expr *Trans_Expr_by_CurVars(Expr *expr, vector<VariableInfo> &Vars);
    Expr *Trans_VariableInfo_to_Expr(VariableInfo var, bool init);
    // void recover_dnf(vector<vector<Expr*>> &dnf);

    vector<vector<Expr *>> Deal_with_condition(Expr *condition, bool not_logic);
    void deduplicate(vector<vector<Expr *>> &dnf);

    void delete_expr_by_var(string var_name);
    void Update_Vars(bool init);
    void copy_after_update(int size);
    vector<vector<Expr *>> Out_Loop(Expr *cond, unordered_set<string> &used_vars, vector<vector<Expr *>> &init_DNF, vector<vector<Expr *>> &init_ineq_DNF, vector<vector<VariableInfo>> &vars);

    void Print_Vars();
    void Print_DNF();
    void Print_DNF(vector<vector<Expr *>> DNF);

    void add_vars(VariableInfo &var);
    void add_vars(VariableInfo &var, Expr *expr);
    void add_expr(Expr *expr);
    void add_comment(ACSLComment *comment);
    void add_fundamental_expr(unordered_set<string> &used_vars);
    void add_fundamental_initexpr(unordered_set<string> &used_vars,vector<vector<Expr*>>& dnf);

    void clear();
    static ASTContext *context;

private:
    vector<vector<Expr *>> Deal_with_condition(Expr *condition, bool not_logic, vector<vector<Expr *>> cur);

    int Verified_Loop_Count;
    vector<ACSLComment *> comments;
    // DONE: Process that where the ineq_dnf is generated, where it should be computed, and how to update the var in the inequality_DNF.
    vector<vector<Expr *>> inequality_DNF;
    vector<vector<VariableInfo>> Vars;
    vector<vector<Expr *>> DNF;

    bool InWhileLoop;
    int Inner_Loop_Depth;
    int Inner_Loop_Count;
    vector<VarGraph> Graphs;
};
void Print_DNF(vector<vector<Expr *>> &DNF);
string Print_Expr(Expr *expr);
Expr *NegateExpr(Expr *expr);
Expr *Add_InitSuffix(Expr *expr);
DeclRefExpr *createDeclRefExpr(string name);
BinaryOperator *createBinOp(Expr *left, Expr *right,BinaryOperatorKind kind);
IntegerLiteral *createIntegerLiteral(int val);
Expr* replace_expr_for_var(Expr* expr,string origin_name,string new_name);
Constraint_System *Trans_Expr_to_Constraints(Expr *expr, enum TransformationType type, int var_size);
vector<vector<Expr *>> Trans_Polys_to_Exprs(vector<C_Polyhedron> poly,bool init_remove);
vector<vector<Expr *>> Trans_Polys_to_Exprs(vector<C_Polyhedron *> poly,bool init_remove);
bool Traverse_Expr_CheckVars(Expr *expr, const unordered_set<string> &res);
void Traverse_Expr_ForVars(Expr *expr, unordered_set<string> &res);
bool CheckInitSuffix(Expr *expr);
#endif