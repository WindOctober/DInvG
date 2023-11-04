#ifndef CPARSER_UTILITY_H
#define CPARSER_UTILITY_H
#include <clang/AST/AST.h>
#include <clang/AST/RecursiveASTVisitor.h>
#include <ppl.hh>
#include <string>
extern clang::ASTContext* globalContext;

Parma_Polyhedra_Library::Linear_Expression TransformExprtoLinExpr(clang::Expr *expr);

#endif