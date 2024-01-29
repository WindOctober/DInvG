#include "ParserUtility.h"
#include "LinTS.h"
using namespace std;
using namespace clang;
using namespace llvm;

ASTContext* globalContext = nullptr;

vector<C_Polyhedron*> MergeTwoPolyVector(vector<C_Polyhedron*>& left,
                                         vector<C_Polyhedron*>& right) {
    vector<C_Polyhedron*> res;
    if (left.size() == 0)
        return right;
    else if (right.size() == 0)
        return left;
    for (int i = 0; i < left.size(); i++) {
        for (int j = 0; j < right.size(); j++) {
            Constraint_System resCS;
            Constraint_System leftCS = left[i]->minimized_constraints();
            Constraint_System rightCS = right[j]->minimized_constraints();
            for (Constraint tmp : leftCS) {
                resCS.insert(tmp);
            }
            for (Constraint tmp : rightCS) {
                resCS.insert(tmp);
            }
            C_Polyhedron* resPoly = new C_Polyhedron(resCS);
            res.push_back(resPoly);
        }
    }
    return res;
}
vector<bool> MergeTwoBoolVector(vector<bool>& left, vector<bool>& right) {
    vector<bool> res;
    if (left.size() == 0)
        return right;
    else if (right.size() == 0)
        return left;
    for (int i = 0; i < left.size(); i++) {
        for (int j = 0; j < right.size(); j++) {
            res.push_back(left[i] || right[j]);
        }
    }
    return res;
}

vector<C_Polyhedron*> ConnectTwoPolyVector(vector<C_Polyhedron*>& left,
                                           vector<C_Polyhedron*>& right) {
    vector<C_Polyhedron*> res;
    res.insert(res.end(), left.begin(), left.end());
    res.insert(res.end(), right.begin(), right.end());
    return res;
}

vector<bool> ConnectTwoBoolVector(vector<bool>& left, vector<bool>& right) {
    vector<bool> res;
    res.insert(res.end(), left.begin(), left.end());
    res.insert(res.end(), right.begin(), right.end());
    return res;
}
CompoundStmt* CreateCompoundStmt(SmallVector<Stmt*, 8> stmtList) {
    CompoundStmt* compound = CompoundStmt::Create(
        *globalContext, stmtList, SourceLocation(), SourceLocation());
    return compound;
}

BinaryOperator* CreateBinaryOperator(Expr* leftExpr,
                                     Expr* rightExpr,
                                     enum BinaryOperatorKind kind,
                                     QualType exprType) {
    if (leftExpr == NULL || rightExpr == NULL) {
        throw runtime_error(
            "The binary operators you create should not have either the LHS "
            "(Left Hand Side) or RHS (Right Hand Side) as null pointers.");
    }
    FPOptions defaultOption;
    BinaryOperator* binary = new (globalContext)
        BinaryOperator(leftExpr, rightExpr, kind, exprType, VK_RValue,
                       OK_Ordinary, SourceLocation(), defaultOption);
    return binary;
}

DeclRefExpr* CreateVarRefExpr(string varName, QualType varType) {
    VarDecl* vardecl = CreateVarDecl(varName, varType);
    DeclRefExpr* declref = new (globalContext) DeclRefExpr(
        *globalContext, vardecl, false, varType, VK_LValue, SourceLocation());
    return declref;
}

DeclRefExpr* CreateVarRefExpr(VarDecl* vardecl) {
    DeclRefExpr* declref = new (globalContext)
        DeclRefExpr(*globalContext, vardecl, false, vardecl->getType(),
                    VK_LValue, SourceLocation());
    return declref;
}

VarDecl* CreateVarDecl(string varName, QualType varType) {
    DeclContext* declcontext = globalContext->getTranslationUnitDecl();
    VarDecl* vardecl = VarDecl::Create(
        *globalContext, declcontext, SourceLocation(), SourceLocation(),
        &globalContext->Idents.get(varName), varType,
        globalContext->getTrivialTypeSourceInfo(varType), SC_None);
    return vardecl;
}

UnaryOperator* CreateUnaryOperator(Expr* unaryExpr,
                                   enum UnaryOperatorKind kind) {
    UnaryOperator* unary = new (globalContext) UnaryOperator(
        unaryExpr, kind, unaryExpr->getType(), unaryExpr->getValueKind(),
        unaryExpr->getObjectKind(), SourceLocation(), false);
    return unary;
}

WhileStmt* CreateWhileStmt(Stmt* body, Expr* cond) {
    WhileStmt* whilestmt = WhileStmt::Create(*globalContext, nullptr, cond,
                                             body, SourceLocation());
    return whilestmt;
}

IntegerLiteral* createIntegerLiteral(uint64_t value) {
    APInt intVal(32, value, true);
    return IntegerLiteral::Create(*globalContext, intVal, globalContext->IntTy,
                                  SourceLocation());
}

void PrintExpr(Expr* expr) {
    if (!expr) {
        outs() << "<EMPTY>";
        return;
    }
    PrintingPolicy policy(globalContext->getLangOpts());
    policy.SuppressScope = true;
    expr->printPretty(outs(), nullptr, policy);
    llvm::outs().flush();
    return;
}