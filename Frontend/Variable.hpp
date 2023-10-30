#ifndef INV_VARIABLE
#define INV_VARIABLE
#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Analysis/CFG.h"
#include <string>
using namespace std;
using namespace clang;
using namespace llvm;

class VariableInfo
{
public:
    // TODO: allow the variable value to be inequality, which should be differed from the pure value(by assignment).
    VariableInfo();
    string getVarName() const { return VarName; };
    Expr *getVarValue() const { return VarValue; };
    QualType getQualType() const { return VarType; };
    bool getStructurePointer() const { return structure_point_flag; }
    bool getNumericalPointer() const { return numerical_point_flag; }
    bool getStructureArray() const { return structure_array_flag; }
    bool getNumericalArray() const { return numerical_array_flag; }

    static void searchElseInsert(VariableInfo var, vector<VariableInfo> &Vars);
    static Expr *search_for_value(VariableInfo var, vector<VariableInfo> &Vars);
    
    void assign(string varname, Expr *expr, QualType type);
    void assign(Expr *var_expr, Expr *init);

private:
    string VarName;
    Expr *VarValue;
    QualType VarType;
    bool structure_point_flag;
    bool numerical_point_flag;
    bool structure_array_flag;
    bool numerical_array_flag;

public:
    bool operator==(const VariableInfo &other) const
    {
        return VarName == other.VarName &&
               structure_point_flag == other.structure_point_flag &&
               numerical_point_flag == other.numerical_point_flag &&
               structure_array_flag == other.structure_array_flag &&
               numerical_array_flag == other.numerical_array_flag;
    }
};

#endif