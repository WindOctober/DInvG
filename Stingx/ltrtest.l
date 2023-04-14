%{
#include <iostream>
#include <ppl.hh>
using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;

#ifndef MAX_ID_SIZE
#define MAX_ID_SIZE 100
#endif

#include "var-info.h"
#include "Location.h"
#include "TransitionRelation.h"
#include "ltrtest.tab.h"
int linenum;
%}

delim  [ \t]
line [\n]
whitespace {delim}+
digit [0-9]
letter [a-zA-Z_]
ident  {letter}({letter}|{digit})*
number ({digit}+)

%%
propsteps { return PROPS;}
variable {return VARIABLED;}
"+" {return '+';}
"*" {return '*';}
"location" {return LOCATION;}
"transition" {return TRANSITION;}
"Location" {return LOCATION;}
"Transition" {return TRANSITION;}
"invariant" {return INVARIANT;}
"-" {return '-';}
">" {return  GE ;}
"<" {return  LE;}
"=" {return EQ;}
">=" {return GEQ;}
"<=" {return LEQ;}

"," {return ',';}
";" {return ';';}
":" {return ':';}
"(" {return '(';}
")" {return ')';}
"{" {return '{';}
"}" {return '}';}
"[" {return '[';}
"]" {return ']';}
end {return END;}
"'" {return PRIME;}
preserve { return PRES;}

{number} {yylval.integer=atoi((char *) yytext); return INT;}
{ident} {strcpy(yylval.identifier,yytext); return IDENT;}
{whitespace} 
{line} {linenum++;}

"#" {  /* Comment line */
   int c;
   c=yyinput();
   while (c!='\n' &&  c!=EOF){
     c=yyinput();
   }
}


.  {printf("Unknown Character in line %d : %s -- Ignored\n", linenum,yytext);}
%%

int yywrap(){
return 1;
}
