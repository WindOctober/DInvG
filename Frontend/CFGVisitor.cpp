#include "CFGVisitor.hpp"

set<string> Main_Functions;
set<string> Visited_Functions;

void CFGVisitor::TraverseCFG(unique_ptr<CFG>& cfg){
    stack<const CFGBlock*> BlockStack;
    set<const CFGBlock*> Visited;
    BlockStack.push(&cfg->getEntry());
    outs()<<"the entry block of the function is: Basic Block "<<(&cfg->getEntry())->getBlockID()<<"\n";
    outs()<<"the exit block of the function is: Basic Block "<<(&cfg->getExit())->getBlockID()<<"\n";
    while(!BlockStack.empty()){
        const CFGBlock* cur=BlockStack.top();
        BlockStack.pop();
        if (!cur) return;
        if (Visited.count(cur)) continue;
        Visited.insert(cur);


        const clang::Stmt *terminator;
        terminator = cur->getTerminator().getStmt();
        outs()<<"\tBasicBlock:"<<cur->getBlockID()<<"\n";
        
        if (!cur->empty()){
            for (const auto &element : *cur) {
                if (const Stmt *stmt = element.castAs<CFGStmt>().getStmt()) {
                    string stmt_str;
                    raw_string_ostream ostream(stmt_str);
                    stmt->printPretty(ostream,nullptr,pp);
                    ostream.flush();
                    
                    outs()<<"\t\t\tStatement type:"<<stmt->getStmtClassName()<<"\n";
                    outs()<<"\t\t\tStatement:"<<stmt_str<<"\n";
                }
            }
            
            if (terminator){
                string condition;
                raw_string_ostream ostream(condition);
                terminator->printPretty(ostream,nullptr,pp);
                ostream.flush();
                outs()<<"\t\t\tConditional jump with condition: "<<terminator->getStmtClassName()<<"\n";
            }
        }
        for(auto it=cur->succ_begin();it && it!=cur->succ_end();it++){
            const CFGBlock* succ=*it;
            BlockStack.push(*it);
            if (!terminator)
                outs()<<"\t\t\tsucc Basic Block is :"<<succ->getBlockID()<<"\n";
            else{
                if (clang::isa<clang::ForStmt>(terminator)){
                    const CFGBlock* Body_Block=*it;
                    it++;
                    if (!(*it)){
                        outs()<<"\t\t\tsucc Exit Loop Block is :"<<Body_Block->getBlockID()<<'\n';
                        continue;
                    }
                    const CFGBlock* Exit_Block=*it;
                    if (it==cur->succ_end()){
                        outs()<<"\t\t\tsucc Exit Loop Block is :"<<Body_Block->getBlockID()<<'\n';
                    }
                    else{
                        outs()<<"\t\t\tsucc Loop body Block is :"<<Body_Block->getBlockID()<<'\n';
                        outs()<<"\t\t\tsucc Exit Loop Block is :"<<Exit_Block->getBlockID()<<'\n';
                        BlockStack.push(Exit_Block);
                    }
                }
                else if (clang::isa<clang::IfStmt>(terminator)){
                    if (!succ){
                        error_output("\tunspecified mode for if statement. As there exists no then branch of if statement.");
                    }
                    const CFGBlock* Then_Block=*it;
                    it++;
                    if (!(*it)){
                        outs()<<"\t\t\tsucc Then Block is :"<<Then_Block->getBlockID()<<'\n';
                        continue;
                    }
                    const CFGBlock* Else_Block=*it;
                    outs()<<"\t\t\tsucc Then Block is :"<<Then_Block->getBlockID()<<'\n';
                    if (it!=cur->succ_end()){
                        outs()<<"\t\t\tsucc Else Block is :"<<Else_Block->getBlockID()<<'\n';
                        BlockStack.push(Else_Block);
                    }
                }
                else if (clang::isa<clang::WhileStmt>(terminator)){
                    const CFGBlock* Body_Block=*it;
                    it++;
                    if (!(*it)){
                        outs()<<"\t\t\tsucc Exit Loop Block is :"<<Body_Block->getBlockID()<<'\n';
                        continue;
                    }
                    const CFGBlock* Exit_Block=*it;
                    if (it==cur->succ_end()){
                        outs()<<"\t\t\tsucc Exit Loop Block is :"<<Body_Block->getBlockID()<<'\n';
                    }
                    else{
                        outs()<<"\t\t\tsucc Loop body Block is :"<<Body_Block->getBlockID()<<'\n';
                        outs()<<"\t\t\tsucc Exit Loop Block is :"<<Exit_Block->getBlockID()<<'\n';
                        BlockStack.push(Exit_Block);
                    }
                }
                else if (clang::isa<clang::ReturnStmt>(terminator)){
                    outs()<<"\t\t\tsucc Return Block is :"<<succ->getBlockID()<<"\n";
                }
            }
        }
    }
}

bool CFGVisitor::VisitCallExpr(CallExpr *CE) {
    if (VS!=VisitorState::Main) return true;
    FunctionDecl *callee = CE->getDirectCallee();
    if (callee && Visited_Functions.count(callee->getNameAsString())==0) {
        SourceManager &SM = context->getSourceManager();
        if (!SM.isInMainFile(callee->getLocation())) return true;
        Visited_Functions.insert(callee->getNameAsString());
        auto cfg=CFG::buildCFG(callee,callee->getBody(),context,CFG::BuildOptions());
        outs()<<"CalleeFunction:"<<callee->getNameAsString()<<"\n";
        TraverseCFG(cfg);
    }
    return true;
}
bool CFGVisitor::VisitFunctionDecl(FunctionDecl *func) {
    SourceManager &SM = context->getSourceManager();
    if (!SM.isInMainFile(func->getLocation())) return true;
    if (VS==VisitorState::Collect_All_Function){
        Main_Functions.insert(func->getNameAsString());
        return true;
    }
    if (func->getNameAsString()=="main" || Main_Functions.count("main")==0) {
        auto cfg=CFG::buildCFG(func,func->getBody(),context,CFG::BuildOptions());
        outs()<<"Function:"<< func->getNameAsString()<<"\n";
        TraverseCFG(cfg);
    }
    return true;
}