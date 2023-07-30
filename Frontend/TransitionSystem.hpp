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
#include "var-info.h"
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




class TransitionSystem
{
public:
    // DONE: process the transformation from the Expr* to Constraint*.
    // DONE: process the generation of the Locations and Transitions.
    // DONE: process the merge of two transition system while split by if statement.
    
    void ComputeInv(Expr *condition, unordered_set<string> vars_in_dnf, vector<C_Polyhedron> init_polys,var_info* total_info);

    void EliminatePath(var_info* total_info);
    void EliminateArray();
    void InitializeLocTrans(int locsize, Expr *condition, var_info* total_info);

    void InitCanonical(int size);
    TransitionSystem();
    TransitionSystem(TransitionSystem &other);

    bool CheckArrayExist();
    bool CheckArrayIncr(ArrIndex RecArrIndex);
    bool CheckModeOne();
    bool CheckModeTwo(string &FlagVar);
    bool CheckModeThree();
    void ArrayInvariantProcess();
    void ArrayInvariantProcessModeOne();
    void ArrayInvariantProcessModeTwo(string FlagVar);
    void ArrayInvariantProcessModeThree();
    
    void ProcessSkipDNF(vector<vector<Expr *>> &dnf);
    // void Construct_Graph();
    void AfterLoop(vector<vector<Expr *>> &dnf, unordered_set<string> &UsedVars);

    void ClearIneqDNF() { InequalityDNF.clear(); }
    
    vector<vector<Expr *>> getDNF() { return DNF; }
    int getVerifiedLoop() {return Verified_Loop_Count;}
    vector<vector<VariableInfo>> getVars() { return Vars; }
    vector<ACSLComment *> getComments() { return comments; }
    vector<vector<Expr *>> getIneqDNF() { return InequalityDNF; }
    unordered_set<string> getUsedVars(Expr *cond, Expr *increment);
    ACSLComment *getCurComment() { return comments[comments.size() - 1]; }
    

    static TransitionSystem MergeTransystem(TransitionSystem &left_trans, TransitionSystem &right_trans);
    void MergeCond(Expr *condition, bool updated);
    void MergeIneqDNF(vector<vector<Expr *>> &dnf);
    void MergeComments(vector<ACSLComment *> &comment);
    unordered_set<string> MergeFuncCall(vector<vector<Expr*>> &function_dnf,CallExpr* callexpr,string new_return_name,unordered_set<string> global_vars);
    void Split_If();

    void init();
    void InLoop();
    Expr *TransExprbyCurVars(Expr *expr, vector<VariableInfo> &Vars);
    Expr *TransVartoExpr(VariableInfo var, bool init);
    // void recover_dnf(vector<vector<Expr*>> &dnf);

    vector<vector<Expr *>> DealwithCond(Expr *condition, bool not_logic);
    void deduplicate(vector<vector<Expr *>> &dnf);

    void delete_expr_by_var(string var_name);
    void UpdateVars(bool init);
    void CopyAfterUpdate(int size);
    vector<vector<Expr *>> OutLoop(Expr *cond, unordered_set<string> &UsedVars, vector<vector<Expr *>> &InitDNF, vector<vector<Expr *>> &InitIneqDNF, vector<vector<VariableInfo>> &vars, unordered_set<string> &LocalVars);

    void PrintVars();
    void PrintDNF();
    void PrintDNF(vector<vector<Expr *>> DNF);

    void AddVars(VariableInfo &var);
    void AddVars(VariableInfo &var, Expr *expr);
    void AddExpr(Expr *expr);
    void AddComment(ACSLComment *comment);
    void AddFundExpr(unordered_set<string> &UsedVars);
    void AddFundInitexpr(unordered_set<string> &UsedVars,vector<vector<Expr*>>& dnf);

    void clear();
    static ASTContext *context;
private:
    vector<vector<Expr *>> DealwithCond(Expr *condition, bool not_logic, vector<vector<Expr *>> cur);

    int Verified_Loop_Count;
    vector<ACSLComment *> comments;
    // DONE: Process that where the RecIneqDNF is generated, where it should be computed, and how to update the var in the InequalityDNF.
    vector<vector<Expr *>> InequalityDNF;
    vector<vector<VariableInfo>> Vars;
    vector<vector<Expr *>> DNF;
    
    Variables_Set project_set;
    bool InWhileLoop;
    int Inner_Loop_Depth;
    int Inner_Loop_Count;
};
extern vector<ArrIndex> ArrayIndex;
void PrintDNF(vector<vector<Expr *>> &DNF);
string PrintExpr(Expr *expr);
Expr *NegateExpr(Expr *expr);
Expr *Add_InitSuffix(Expr *expr);
DeclRefExpr *createDeclRefExpr(string name);
BinaryOperator *createBinOp(Expr *left, Expr *right,BinaryOperatorKind kind);
IntegerLiteral *createIntegerLiteral(int val);
Expr* ReplaceExprForVar(Expr* expr,string origin_name,string new_name);
Constraint_System *TransExprtoConstraints(Expr *expr, enum TransformationType type, var_info* total_info);
vector<vector<Expr *>> TransPolystoExprs(vector<C_Polyhedron> poly,bool init_remove);
vector<vector<Expr *>> TransPolystoExprs(vector<C_Polyhedron *> poly,bool init_remove);
bool TraverseExprCheckVars(Expr *expr, const unordered_set<string> &res);
void TraverseExprForVars(Expr *expr, unordered_set<string> &res);
bool CheckInitSuffix(Expr *expr);
#endif