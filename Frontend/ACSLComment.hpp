#ifndef INV_ACSLCOMMENT
#define INV_ACSLCOMMENT
#include<vector>
#include<unordered_set>
#include<string>
#include<ppl.hh>
#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
using namespace std;
using namespace clang;
using namespace llvm;

struct ArrIndex{
    string IndexName;
    int InitIndex=-1;
};

class ACSLComment{
    public:
        enum class CommentType{LOOP,ASSERT,FUNCTION,MODEONEINV,MODETWOALLINV,MODETWOEXISTINV};
        ACSLComment(int line_number,enum CommentType type):line(line_number),comment_type(type){}
        void dump(ofstream& out,ASTContext* context);
        void add_invariant(vector<vector<Expr*>> exprs,bool connect);
        void AddArrayInv(Expr* expr,ArrIndex index);
        void AddFlagExpr(Expr* expr);
        void AddAssignVars(string name);
        void AddAssignVars(vector<string> vars);
        void AddAssignVars(unordered_set<string>& vars);
        void set_assertion(Expr* assertion);
        void deduplication();
        int getLineNum() {return line;}
        vector<vector<Expr *>>& GetInv() {return LoopInv;}
        
    private:
        enum CommentType comment_type;
        vector<vector<Expr *>> LoopInv;
        Expr* Assertion;
        vector<Expr*> ArrayInv;
        vector<Expr*> FlagExpr;
        vector<ArrIndex> Index;
        int line;
        unordered_set<string> assign_vars;
};
#endif