%option noyywrap
%{
    #include"LinTS.h"
    #include"Location.h"
    #include"TransitionRelation.h"
    #include"var-info.h"
    #include<stdlib.h>
    #include"ppl.hh"
    #include "parser.h"
    #include<iostream>
    using namespace std;
    using namespace Parma_Polyhedra_Library;
    using namespace Parma_Polyhedra_Library::IO_Operators;
    extern void yyerror(LinTS* root,const char *s);
    
%}

id [a-zA-Z_][a-zA-Z0-9_]*
digit [0-9]
whitespace [ \t]+
%%

"Variable"|"variable" {return tokenVariable;}
"Location"|"location" {return tokenLocation;}
"transition"|"Transition" {return tokenTransition;}
"invariant"|"Invariant" {return tokenInvariant;}
"end" {return tokenEnd;}
{id} {yylval.str=strdup(yytext); return tokenId;}
{digit}+ {yylval.val=atoi(yytext); return tokenNumber;}
"'" {return tokenPrimed;}
":" {return tokenColon;}
"(" {return tokenLParen;}
")" {return tokenRParen;}
"{" {return tokenLBrace;}
"}" {return tokenRBrace;}
"[" {return tokenLBracket;}
"]" {return tokenRBracket;}
"," {return tokenComma;}
"+" {return tokenPlus;}
"-" {return tokenMinus;}
"*" {return tokenMulti;}
"<=" {return tokenLE;}
">=" {return tokenGE;}
"<" {return tokenLT;}
">" {return tokenGT;}
"=" {return tokenEQ;}

{whitespace} {}
#.* {}
. {cout<<"unknown character : "<<yytext<<endl;}
%%