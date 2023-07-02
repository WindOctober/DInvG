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

class ACSLComment{
    public:
        enum class CommentType{LOOP,ASSERT,FUNCTION};
        ACSLComment(int line_number,enum CommentType type):line(line_number),comment_type(type){}
        void dump(ofstream& out,ASTContext* context);
        void add_invariant(vector<vector<Expr*>> exprs,bool connect);
        void add_assign_vars(string name);
        void add_assign_vars(vector<string> vars);
        void add_assign_vars(unordered_set<string>& vars);
        void set_assertion(Expr* assertion);
        void deduplication();
        vector<vector<Expr *>>& get_invariant() {return loop_invariant;}
        int get_line_number() {return line;}
        
    private:
        enum CommentType comment_type;
        vector<vector<Expr *>> loop_invariant;
        Expr* Assertion;
        int line;
        unordered_set<string> assign_vars;
};
#endif