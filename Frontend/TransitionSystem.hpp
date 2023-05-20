#ifndef INV_TRANSITIONSYSTEM
#define INV_TRANSITIONSYSTEM
#include"clang/AST/ASTContext.h"
#include"clang/AST/ASTConsumer.h"
#include"clang/AST/RecursiveASTVisitor.h"   
#include"clang/Analysis/CFG.h"
#include "Variable.hpp"
#include<vector>
#include<ppl.hh>
#include<string>

using namespace std;
using namespace clang;
using namespace llvm;

class TransitionSystem{
public:
    // TODO: process the transformation from the Expr* to Constraint*.
    // TODO: process the generation of the Locations and Transitions.
    
    TransitionSystem(ASTContext*& astcontext);
    

    void In_Loop(Expr* cond);
    Expr* Trans_VariableInfo_to_Expr(VariableInfo var);
    Constraint* Trans_Expr_to_Constraint(Expr* expr);
    vector<vector<Expr*>> Deal_with_condition(Expr* condition,bool not_logic,vector<vector<Expr*>> cur);
    vector<vector<Expr*>> Merge_DNF(vector<vector<Expr*>> left_expr,vector<vector<Expr*>> right_expr);
    vector<vector<Expr*>> Connect_DNF(vector<vector<Expr*>> left_expr,vector<vector<Expr*>> right_expr);

    void Out_Loop();
    void Print_DNF();

    void add_vars(VariableInfo var,int left,int right);
    void add_expr(Expr* expr,int left,int right);
    int get_Canonical_count();
    void init_Canonical(int size);
    void add_condition_all(Expr* expr);
    void isPreVar();
    void Split_If();
    ASTContext* context;
private:
    
    vector<vector<VariableInfo>> Vars;
    int Verified_Loop_Count;
    vector<vector<Expr*>> DNF;
    int Canonical_Branch_Count;
    bool InWhileLoop;
    bool pre_var;
    
};

#endif