#include"ACSLComment.hpp"
#include"Library.hpp"
#include<fstream>
void ACSLComment::dump(ofstream& out){
    out<<"\t /*@\n";
    bool flag;
    switch(comment_type){
        case CommentType::LOOP:
            out<<"\t loop invariant\n";
            for(int i=0;i<loop_invariant.size();i++){
                if (i){
                    out<<"\t\t || \n";
                }
                out<<"\t ( \n";
                for(int j=0;j<loop_invariant[i].size();j++){
                    if (j){
                        out<<"\t\t && \n";
                    }
                    out<<"\t ("<<Print_Expr(loop_invariant[i][j])<<")\n";
                }
                out<<"\t ) \n";
            }
            out<<"\t;\n";
            out<<"\t loop assigns ";
            flag=false;
            if (assign_vars.size()==0){
                LOG_WARNING("No assignments?");
                out<<"\n";
                break;
            }
            for(auto var: assign_vars){
                if (flag)
                    out<<',';
                else
                    flag=true;
                out<<var;
            }
            out<<";\n";
            break;
        case CommentType::ASSERT:
            break;
        case CommentType::FUNCTION:
            break;
    }
    out<<"\t */\n";
    return;
}
void ACSLComment::add_invariant(vector<vector<Expr*>> exprs){
    loop_invariant=Connect_DNF(loop_invariant,exprs);
    return;
}
void ACSLComment::add_invariant(vector<C_Polyhedron> polys){
    loop_invariant=Connect_DNF(loop_invariant,Trans_Polys_to_Exprs(polys));
    return;
}
void ACSLComment::add_assign_vars(string name){
    assign_vars.insert(name);
    return;
}
void ACSLComment::add_assign_vars(vector<string> vars){
    assign_vars.insert(vars.begin(),vars.end());
    return;
}
void ACSLComment::add_assign_vars(unordered_set<string>& vars){
    assign_vars.insert(vars.begin(),vars.end());
    return;
}
void ACSLComment::set_assertion(Expr* assertion){
    Assertion=assertion;
    return;
}