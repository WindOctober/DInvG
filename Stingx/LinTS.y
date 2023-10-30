%{
    #include"LinTS.h"
    #include"Location.h"
    #include"TransitionRelation.h"
    #include"var-info.h"
    #include<stdlib.h>
    #include"ppl.hh"
    extern int yylex();
    using namespace std;
    using namespace Parma_Polyhedra_Library;
    using namespace Parma_Polyhedra_Library::IO_Operators;
    void yyerror(LinTS* root, const char *s);
%}
%code requires {
   #include "LinTS.h"
}
%parse-param { LinTS* root }
%union{
    int val;
    char* str;
    LinTS* ts;
    Linear_Expression* lin;
    Constraint* cs;
    C_Polyhedron *poly;
}

%token <val> tokenNumber
%token <str> tokenId
%token tokenVariable tokenLocation tokenTransition tokenInvariant
%token tokenEnd tokenPrimed tokenColon tokenLParen tokenRParen
%token tokenLBrace tokenRBrace tokenLBracket tokenRBracket tokenComma
%token tokenPlus tokenMinus tokenMulti tokenLE tokenGE tokenLT tokenGT tokenEQ

%type <ts> Whole
%type VariableDeclare VariableList SystemDeclare LocationDeclare
%type TransitionDeclare InvariantDeclare
%type <poly> LocalPoly PrimedPoly
%type <cs> Constraint
%type <lin> LinExpr

%nonassoc tokenLE tokenGE tokenLT tokenGT tokenEQ
%left tokenPlus tokenMinus
%left tokenMulti
%right tokenUMinus

%%

Whole:
    VariableDeclare SystemDeclare tokenEnd
    {
        $$=root;
    }
;

VariableDeclare:
    tokenVariable tokenLBracket VariableList tokenRBracket
;

VariableList:
    tokenId VariableList
    {
        root->addVariable($1);
    }
|   tokenId
    {
        root->addVariable($1);
    }
;

SystemDeclare:
    LocationDeclare SystemDeclare
|   TransitionDeclare SystemDeclare
|   InvariantDeclare SystemDeclare
|   LocationDeclare
|   TransitionDeclare
|   InvariantDeclare
;

LocationDeclare:
    tokenLocation tokenId LocalPoly
    {
        root->addLocInit($2,$3);
    }
|   tokenLocation tokenId tokenColon LocalPoly
    {
        root->addLocInit($2,$4);
    }
|   tokenLocation tokenId
    {
        root->addLocInit($2,NULL);
    }
;

TransitionDeclare:
    tokenTransition tokenId tokenColon tokenId tokenComma PrimedPoly
    {
        root->addTransRel($2,$4,NULL,$6);
    }
|   tokenTransition tokenId tokenColon tokenId tokenComma tokenId tokenComma PrimedPoly
    {
        root->addTransRel($2,$4,$6,$8);
    }
;

InvariantDeclare:
    tokenInvariant tokenId tokenColon LocalPoly
    {
        root->setLocPreInv($2,$4);        
    } 
;

LocalPoly:
    Constraint LocalPoly
    {
        C_Polyhedron* poly=$2;
        poly->add_constraint(*$1);   
        $$=poly;
    }
|   Constraint
    {
        C_Polyhedron* poly=new C_Polyhedron(root->getVarNum(),UNIVERSE);
        poly->add_constraint(*$1);
        $$=poly;
    }
;

PrimedPoly:
    Constraint PrimedPoly
    {
        C_Polyhedron* poly=$2;
        poly->add_constraint(*$1);   
        $$=poly;
    }
|   Constraint
    {
        C_Polyhedron* poly=new C_Polyhedron(root->getVarNum()*2,UNIVERSE);
        poly->add_constraint(*$1);
        $$=poly;
    }
;



Constraint:
    LinExpr tokenLE LinExpr
    {
        $$=new Constraint(*$1 <= *$3);
        delete($1);
        delete($3);
    }
|   LinExpr tokenGE LinExpr
    {
        $$=new Constraint(*$1 >= *$3);
        delete($1);
        delete($3);
    }
|   LinExpr tokenGT LinExpr
    {
        $$=new Constraint(*$1 > *$3);
        delete($1);
        delete($3);
    }
|   LinExpr tokenLT LinExpr
    {
        $$=new Constraint(*$1 < *$3);
        delete($1);
        delete($3);
    }
|   LinExpr tokenEQ LinExpr
    {
        $$=new Constraint(*$1 == *$3);
        delete($1);
        delete($3);
    }
;

LinExpr:
    tokenLParen LinExpr tokenRParen
    {
        $$=$2;
    }
|   LinExpr tokenPlus LinExpr
    {
        $$=$1;
        (*$1)+=(*$3);
        delete $3;
    }
|   LinExpr tokenMinus LinExpr
    {
        $$=$1;
        (*$1)-=(*$3);
        delete $3;
    }
|   tokenNumber tokenMulti tokenId
    {
        int index=root->getVarIndex($3);
        $$=new Linear_Expression($1 * Variable(index));
    }
|   tokenNumber tokenMulti tokenPrimed tokenId
    {
        int index=root->getVarIndex($4);
        int tmpVarNum=root->getVarNum();
        $$=new Linear_Expression($1 * Variable(index+tmpVarNum));
    }
|   tokenNumber
    {
        $$=new Linear_Expression($1);
    }
|   tokenMinus LinExpr %prec tokenUMinus
    {
        $$=$2;
        (*$2)=-(*$2);
    }
|   tokenId
    {
        int index=root->getVarIndex($1);
        $$=new Linear_Expression(Variable(index));
    }
|   tokenPrimed tokenId
    {
        int index=root->getVarIndex($2);
        int tmpVarNum=root->getVarNum();
        $$=new Linear_Expression(Variable(tmpVarNum+index));
    }
;

%%

void yyerror(LinTS* root,const char *s) {
    fprintf(stderr, "Error: %s ", s);
}
