#include"ACSLComment.hpp"
#include"Library.hpp"
#include"TransitionSystem.hpp"
#include"var-info.h"
#include<fstream>
extern var_info* info;
void ACSLComment::dump(ofstream& out,ASTContext* context){
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
                flag=false;
                for(int j=0;j<loop_invariant[i].size();j++){
                    
                    PrintingPolicy Policy(context->getLangOpts());
                    string str;
                    llvm::raw_string_ostream rso(str);
                    loop_invariant[i][j]->printPretty(rso, nullptr, Policy);
                    rso.flush();
                    if (str.find(INITSUFFIX)!=str.npos) continue;
                    if (flag){
                        out<<"\t\t && \n";
                    }
                    else flag=true;
                    out<<"\t ("<<str<<")\n";
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

void ACSLComment::deduplication(){
    vector<C_Polyhedron*> polys;
    LOG_INFO("loop_invariant before deduplication");
    Print_DNF(loop_invariant);
    for(int i=0;i<loop_invariant.size();i++){
        
        C_Polyhedron *p=new C_Polyhedron(int(info->get_dimension()/2),UNIVERSE);
        for(int j=0;j<loop_invariant[i].size();j++){
            if (!CheckInitSuffix(loop_invariant[i][j]))
                p->add_constraints(*Trans_Expr_to_Constraints(loop_invariant[i][j],TransformationType::Loc,info->get_dimension()/2));
            else LOG_INFO(to_string(j));
        }
        if (p->is_empty()){
            loop_invariant.erase(loop_invariant.begin()+i);
            i--;
            continue;
        }
        bool flag=true;
        for(int j=0;j<polys.size();j++){
            if (*polys[j]==*p){
                flag=false;
                break;
            }
        }
        if (!flag){
            loop_invariant.erase(loop_invariant.begin()+i);
            i--;
        }
        else polys.push_back(p);
    }
    LOG_INFO("Final ACSL invariant Before Add Remain:");
    Print_DNF(loop_invariant);
    return;
}

void ACSLComment::add_invariant(vector<vector<Expr*>> exprs,bool connect){
    if (connect)
        loop_invariant=Connect_DNF(loop_invariant,exprs);
    else
        loop_invariant=Merge_DNF(loop_invariant,exprs);
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