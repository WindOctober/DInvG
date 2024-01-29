#ifndef CPARSER_UTILITY_H
#define CPARSER_UTILITY_H
#include <clang/AST/AST.h>
#include <clang/AST/RecursiveASTVisitor.h>
#include <ppl.hh>
#include <string>
#include <vector>
extern clang::ASTContext* globalContext;

std::vector<Parma_Polyhedra_Library::C_Polyhedron*> MergeTwoPolyVector(
    std::vector<Parma_Polyhedra_Library::C_Polyhedron*>& left,
    std::vector<Parma_Polyhedra_Library::C_Polyhedron*>& right);
std::vector<Parma_Polyhedra_Library::C_Polyhedron*> ConnectTwoPolyVector(
    std::vector<Parma_Polyhedra_Library::C_Polyhedron*>& left,
    std::vector<Parma_Polyhedra_Library::C_Polyhedron*>& right);

std::vector<bool> MergeTwoBoolVector(std::vector<bool>& left,
                                     std::vector<bool>& right);
std::vector<bool> ConnectTwoBoolVector(std::vector<bool>& left,
                                       std::vector<bool>& right);
clang::CompoundStmt* CreateCompoundStmt(
    llvm::SmallVector<clang::Stmt*, 8> stmtList);
clang::BinaryOperator* CreateBinaryOperator(clang::Expr* leftExpr,
                                            clang::Expr* rightExpr,
                                            enum clang::BinaryOperatorKind kind,
                                            clang::QualType exprType);
clang::VarDecl* CreateVarDecl(std::string varName, clang::QualType varType);
clang::DeclRefExpr* CreateVarRefExpr(std::string varName,
                                     clang::QualType varType);
clang::DeclRefExpr* CreateVarRefExpr(clang::VarDecl* vardecl);
clang::UnaryOperator* CreateUnaryOperator(clang::Expr* unaryExpr,
                                          enum clang::UnaryOperatorKind kind);
clang::WhileStmt* CreateWhileStmt(clang::Stmt* body, clang::Expr* cond);
clang::IntegerLiteral* createIntegerLiteral(uint64_t value);
void PrintExpr(clang::Expr* expr);
#endif