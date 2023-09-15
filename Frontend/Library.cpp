#include "Library.hpp"
#include "var-info.h"
#include <unordered_set>
extern var_info *info;
int GlobalIndexCount = 0;
ASTContext *astcontext;
void Log(const string &level, const string &function, int line, string msg)
{
    outs() << "\n[" << level << " " << function << ":" << line << "] " << msg;
}

string MakeIndexName(){
    GlobalIndexCount++;
    return INDEXPREFIX + to_string(GlobalIndexCount);
}
vector<vector<Expr *>> AppendDNF(vector<vector<Expr *>> left_expr, vector<vector<Expr *>> right_expr)
{
    assert(left_expr.size() == right_expr.size());
    vector<vector<Expr *>> merged_expr;
    vector<Expr *> rec_expr;
    for (int i = 0; i < left_expr.size(); i++)
    {
        rec_expr.insert(rec_expr.end(), left_expr[i].begin(), left_expr[i].end());
        rec_expr.insert(rec_expr.end(), right_expr[i].begin(), right_expr[i].end());
        merged_expr.push_back(rec_expr);
        rec_expr.clear();
    }
    return merged_expr;
}

vector<vector<Expr *>> Merge_DNF(vector<vector<Expr *>> left_expr, vector<vector<Expr *>> right_expr)
{
    if (left_expr.size() == 0)
        return right_expr;
    if (right_expr.size() == 0)
        return left_expr;
    vector<vector<Expr *>> merged_expr;
    vector<Expr *> rec_expr;
    for (int i = 0; i < left_expr.size(); i++)
    {
        for (int j = 0; j < right_expr.size(); j++)
        {
            rec_expr.insert(rec_expr.end(), left_expr[i].begin(), left_expr[i].end());
            rec_expr.insert(rec_expr.end(), right_expr[j].begin(), right_expr[j].end());
            merged_expr.push_back(rec_expr);
            rec_expr.clear();
        }
    }
    return merged_expr;
}

vector<vector<Expr *>> ConnectDNF(vector<vector<Expr *>> left_expr, vector<vector<Expr *>> right_expr)
{
    if (left_expr.size() == 0)
        return right_expr;
    vector<vector<Expr*>> rec_expr;
    rec_expr.insert(rec_expr.end(), left_expr.begin(), left_expr.end());
    rec_expr.insert(rec_expr.end(), right_expr.begin(), right_expr.end());
    return rec_expr;
}

vector<C_Polyhedron> Merge_Poly(vector<C_Polyhedron> &left_poly, vector<C_Polyhedron> &right_poly)
{
    // NOTE: keep an eye on the polyhedron's dimensions.
    vector<C_Polyhedron> res;
    if (right_poly.size() == 0)
        return left_poly;
    if (left_poly.size() == 0)
        return right_poly;
    for (int i = 0; i < left_poly.size(); i++)
    {
        for (int j = 0; j < right_poly.size(); j++)
        {
            C_Polyhedron poly(info->get_dimension(), UNIVERSE);
            poly.add_constraints(left_poly[i].minimized_constraints());
            poly.add_constraints(right_poly[j].minimized_constraints());
            if (!poly.is_empty())
            {
                res.push_back(poly);
            }
        }
    }
    return res;
}

// vector<vector<vector<string>>> Derive_Vars_From_Poly(vector<C_Polyhedron> &poly, vector<VariableInfo> &vars)
// {
//     vector<vector<vector<string>>> res;
//     res.resize(poly.size());
//     unordered_map<int, string> var_map;
//     for (int i = 0; i < vars.size(); i++)
//     {
//         int index = info->search(vars[i].getVarName().c_str());
//         string name = vars[i].getVarName();
//         var_map.insert(pair<int, string>(Variable(index).id(), name));
//     }
//     for (int i = 0; i < poly.size(); i++)
//     {
//         vector<vector<string>> UsedVars;
//         Constraint_System constraints = poly[i].minimized_constraints();
//         for (auto &constraint : constraints)
//         {
//             const auto &le = constraint.expression();
//             vector<string> used;
//             for (auto it = le.begin(); it != le.end(); ++it)
//             {
//                 Variable var = it.variable();
//                 int var_id = var.id();
//                 if (var_map.find(var_id) != var_map.end())
//                 {
//                     used.push_back(var_map[var_id]);
//                 }
//                 else
//                 {
//                     LOGWARN("UnFounded Variable with var id is: " + to_string(var_id));
//                 }
//             }
//             UsedVars.push_back(used);
//         }
//         res[i] = UsedVars;
//     }
//     return res;
// }