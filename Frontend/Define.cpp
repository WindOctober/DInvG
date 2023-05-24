#include "Define.hpp"
#include "CFGVisitor.hpp"

void Log(const string &level, const string &function, int line, string msg)
{
    outs() << "\n[" << level << " " << function << ":" << line << "] " << msg;
}

string Print_Expr(Expr *expr)
{
    PrintingPolicy Policy(TransitionSystem::context->getLangOpts());
    string str;
    llvm::raw_string_ostream rso(str);
    expr->printPretty(rso, nullptr, Policy);
    rso.flush();
    return str;
}