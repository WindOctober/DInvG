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
    // TODO: process the generation of the Locations and 
    void add_vars(VariableInfo var,int left,int right);
    TransitionSystem(ASTContext* context);


    void In_Loop(Expr* cond);
    vector<vector<Expr*>> Deal_with_condition(Expr* condition,bool not_logic,vector<vector<Expr*>> cur);
    vector<vector<Expr*>> Merge_DNF(vector<vector<Expr*>> left_expr,vector<vector<Expr*>> right_expr);
    vector<vector<Expr*>> Connect_DNF(vector<vector<Expr*>> left_expr,vector<vector<Expr*>> right_expr);
    void Out_Loop();
    int get_Canonical_count();
    void init_Canonical(int size);
    void add_condition_all(Expr* expr);
    void Split_If();

private:
    Constraint* Trans_Expr_to_Constraint(Expr* expr);
    vector<vector<VariableInfo>> Vars;
    int Verified_Loop_Count;
    vector<vector<Expr*>> DNF;
    int Canonical_Branch_Count;
    bool InWhileLoop;
    ASTContext* context;
};

#endif