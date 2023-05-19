#ifndef INV_DNFEXPR
#define INV_DNFEXPR
#include"clang/AST/ASTContext.h"
#include"clang/AST/ASTConsumer.h"
#include"clang/AST/RecursiveASTVisitor.h"
#include"clang/Analysis/CFG.h"
#include"Variable.hpp"
#include<vector>
#include<string>
using namespace clang;
using namespace std;

class TransitionSystem{
public:
    void add_vars(VariableInfo var);
     

private:
    vector<VariableInfo> Vars;
};a

#endif