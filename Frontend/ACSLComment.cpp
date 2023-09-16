#include "ACSLComment.hpp"
#include "Library.hpp"
#include "TransitionSystem.hpp"
#include "var-info.h"
#include <regex>
#include <fstream>
extern var_info *info;

string ReplaceArrayIndex(const string &str, const string &RealIndexName, const string &IndexName)
{
    string result = str;
    regex pattern("\\[(.*?)\\]");

    smatch matches;
    string::const_iterator searchStart(str.cbegin());

    while (regex_search(searchStart, str.cend(), matches, pattern))
    {
        string match = matches[1].str();
        if (match == RealIndexName)
        {
            result = regex_replace(result, regex("\\[" + RealIndexName + "\\]"), "[" + IndexName + "]");
        }
        else
        {
            LOGWARN(str);
            exit(-1);
        }
        searchStart = matches.suffix().first;
    }

    return result;
}

void ACSLComment::dump(ofstream &out, ASTContext *context)
{
    out << "\t /*@\n";
    bool flag;
    PrintingPolicy Policy(context->getLangOpts());
    switch (comment_type)
    {
    case CommentType::MODEONEINV:
        assert(ArrayInv.size() == Index.size());
        for (int i = 0; i < ArrayInv.size(); i++)
        {
            out << "\t loop invariant\t";
            string IndexName = "IndexI";
            string RealIndexName = Index[i].IndexName;
            Expr *Inv = ArrayInv[i];
            Inv = ReplaceExprForVar(Inv, RealIndexName, IndexName);
            string ExprStr;
            raw_string_ostream rso(ExprStr);
            out << "\\forall integer " + IndexName + "; 0 <= " + IndexName + " < " + RealIndexName + " ==> ";
            Inv->printPretty(rso, NULL, Policy);
            rso.flush();
            out << ExprStr << " ;\n";
        }
        break;
    case CommentType::MODETWOEXISTINV:
        assert(ArrayInv.size() == FlagExpr.size());
        assert(ArrayInv.size() == Index.size());
        for (int i = 0; i < ArrayInv.size(); i++)
        {
            out << "\t loop invariant\t";
            string FlagStr;
            raw_string_ostream Flagrso(FlagStr);
            FlagExpr[i]->printPretty(Flagrso, NULL, Policy);
            Flagrso.flush();
            out << FlagStr << " ==> ";
            string IndexName = "IndexI";
            string RealIndexName = Index[i].IndexName;
            Expr *Inv = ArrayInv[i];
            Inv = ReplaceExprForVar(Inv, RealIndexName, IndexName);
            string ExprStr;
            raw_string_ostream rso(ExprStr);
            out << "\\exists integer " + IndexName + "; 0 <= " + IndexName + " < " + RealIndexName + " && ";
            Inv->printPretty(rso, NULL, Policy);
            rso.flush();
            out << ExprStr << " ;\n";
        }
        break;
    case CommentType::MODETWOALLINV:
        assert(ArrayInv.size() == FlagExpr.size());
        for (int i = 0; i < ArrayInv.size(); i++)
        {
            out << "\t loop invariant\t";
            string FlagStr;
            raw_string_ostream Flagrso(FlagStr);
            FlagExpr[i]->printPretty(Flagrso, NULL, Policy);
            Flagrso.flush();
            out << FlagStr << " ==> ";
            string IndexName = "IndexI";
            string RealIndexName = Index[i].IndexName;
            Expr *Inv = ArrayInv[i];
            Inv = ReplaceExprForVar(Inv, RealIndexName, IndexName);
            string ExprStr;
            raw_string_ostream rso(ExprStr);
            out << "\\forall integer " + IndexName + "; 0 <= " + IndexName + " < " + RealIndexName + " ==> ";
            Inv->printPretty(rso, NULL, Policy);
            rso.flush();
            out << ExprStr << " ;\n";
        }
        break;
    case CommentType::LOOP:
        out << "\t loop invariant\n";
        for (int i = 0; i < LoopInv.size(); i++)
        {
            if (i)
            {
                out << "\t||";
            }
            else
                out << "\t  ";
            out << "\t(";
            flag = false;
            for (int j = 0; j < LoopInv[i].size(); j++)
            {
                string str;
                raw_string_ostream rso(str);
                LoopInv[i][j]->printPretty(rso, nullptr, Policy);
                rso.flush();
                if (str.find(INITSUFFIX) != str.npos)
                    continue;
                if (flag)
                {
                    out << " && ";
                }
                else
                    flag = true;
                out << "(" << str << ")";
            }
            out << " )";
            if (i + 1 != LoopInv.size())
                out << "\n";
        }
        out << "\t;\n";
        out << "\t loop assigns ";
        flag = false;
        if (assign_vars.size() == 0)
        {
            LOGWARN("No assignments?");
            out << "\n";
            break;
        }
        for (auto var : assign_vars)
        {
            if (flag)
                out << ',';
            else
                flag = true;
            out << var;
        }
        out << ";\n";
        break;
    case CommentType::ASSERT:
        break;
    case CommentType::FUNCTION:
        break;
    }
    out << "\t */\n";
    return;
}

void ACSLComment::deduplication()
{
    vector<C_Polyhedron *> polys;
    LOGINFO("LoopInv before deduplication");
    PrintDNF(LoopInv);
    for (int i = 0; i < LoopInv.size(); i++)
    {

        C_Polyhedron *p = new C_Polyhedron(int(info->getDim() / 2), UNIVERSE);
        for (int j = 0; j < LoopInv[i].size(); j++)
        {
            if (!CheckInitSuffix(LoopInv[i][j]))
                p->add_constraints(*TransExprtoConstraints(LoopInv[i][j], TransformationType::Loc, info));
            else
                LOGINFO(to_string(j));
        }
        if (p->is_empty())
        {
            LoopInv.erase(LoopInv.begin() + i);
            i--;
            continue;
        }
        bool flag = true;
        for (int j = 0; j < polys.size(); j++)
        {
            if (*polys[j] == *p)
            {
                flag = false;
                break;
            }
        }
        if (!flag)
        {
            LoopInv.erase(LoopInv.begin() + i);
            i--;
        }
        else
            polys.push_back(p);
    }
    LOGINFO("Final ACSL invariant Before Add Remain:");
    PrintDNF(LoopInv);
    return;
}

void ACSLComment::add_invariant(vector<vector<Expr *>> exprs, bool connect)
{
    if (connect)
        LoopInv = ConnectDNF(LoopInv, exprs);
    else
        LoopInv = Merge_DNF(LoopInv, exprs);
    return;
}

void ACSLComment::AddArrayInv(Expr *expr, ArrIndex index)
{
    ArrayInv.push_back(expr);
    Index.push_back(index);
    return;
}

void ACSLComment::AddFlagExpr(Expr *expr)
{
    FlagExpr.push_back(expr);
    return;
}

void ACSLComment::AddAssignVars(string name)
{
    assign_vars.insert(name);
    return;
}
void ACSLComment::AddAssignVars(vector<string> vars)
{
    assign_vars.insert(vars.begin(), vars.end());
    return;
}
void ACSLComment::AddAssignVars(unordered_set<string> &vars)
{
    assign_vars.insert(vars.begin(), vars.end());
    return;
}
void ACSLComment::set_assertion(Expr *assertion)
{
    Assertion = assertion;
    return;
}