%{
#include <iostream>
#include <vector>
#include "var-info.h"
#include "Location.h"
#include "PolyUtils.h"
#include "TransitionRelation.h"
#include "InvariantMap.h"
#include "DualInvariantMap.h"
#include "System.h"
#include "Timer.h"
#include "ppl.hh"
#include "Elimination.h"
#include "Tree.h"

 
   using namespace std;
   using namespace Parma_Polyhedra_Library;
   using namespace Parma_Polyhedra_Library::IO_Operators;

   bool gendrop;
   int num_context;
   bool zero;
   bool one;
   int prop_steps;
   int weave_time;
   bool ch79,bhrz03,dual;
   string projection;
   string tree_prior;
   string some_per_group;
   bool clear_lower_gli = false;
   int clear_lower_gli_depth = -1;
   bool backhere_flag = false;
   int related_location_number;
   int related_transition_number;
   
   C_Polyhedron * trivial, *dualp;
   
#ifndef MAX_ID_SIZE
#define MAX_ID_SIZE 100
#endif
   
#define ONECONTEXT 0
#define GENDROP 1
#define MANYCONTEXT 2
#define BULLSHIT 3
#define NEW_MANYCONTEXT 401
#define NEW_2_MANYCONTEXT 402
#define NEW_3_MANYCONTEXT 403
#define NEWDFS 404
#define NEWDFS_SEQUENCES 405
#define NO_PROJECTION 410
#define KOHLER_ELIMINATE_C 411
#define FARKAS_ELIMINATE_C 412
#define FOUMOT_ELIMINATE_C 413
#define NO_PRIOR 420
#define TARGET_PRIOR1 421
#define TARGET_PRIOR2 422
#define TARGET_PRIOR3 423
#define ONE_PER_GROUP 431
#define TWO_PER_GROUP 432
#define THREE_PER_GROUP 433
#define FOUR_PER_GROUP 434
#define ZERO_ONLY 5
#define ONE_ONLY 6
#define ZERO_ONE 7
#define NO_INSTANTIATION 8
#define NO_CH79 9
#define NO_BHRZ03 10
#define NO_DUAL 11
#define YES_CH79 12
#define YES_BHRZ03 13
#define YES_DUAL 14
#define INV_CHECK 15
#define NO_INV_CHECK 16
   
   
  vector<int> **location_matrix;
  int location_count=0;
  int global_binary_i=0;
  long int global_contains_time=0;
  vector<int> target_prior;

  char err_str[100];
  extern int linenum;
  int dimension;
  var_info * f, *fd, *fm;
  vector<Location *> * loclist;
  vector<TransitionRelation *> * trlist;
  Context *glc;// The global context
  vector<Context *>* children;
  vector<System *> * global_sub_system_list;
  System * global_system;
  Timer total_time;
  Timer weave_timer;
  Timer dfs_traverse_timer;
  Timer single_dfs_traverse_timer;
  Timer collect_timer;
  Timer prune_nodes_timer;
  Timer backtrack_timer;
  Timer single_dfs_sequences_generation_timer;
  Timer single_dfs_sequences_traverse_timer;
  Timer single_merge_sub_sequences_timer;
  long int dfs_traverse_time;
  int collect_time = 0;
  int prune_nodes_time = 0;
  int backtrack_time = 0;
  vector<int> vector_single_collect_time;
  vector<int> vector_single_dfs_traverse_time;
  vector<int> vector_single_dfs_sequences_generation_time;
  vector<int> vector_single_dfs_sequences_traverse_time;
  int single_collect_time;
  int * tt;
  C_Polyhedron * invd;

  bool inv_check;
   
   
  extern int yyparse();
  extern int yylex();
  void yyerror(char const * x);
  void yyerror(string  const & x);
  void collect_generators(vector<Context *> * children , Generator_System & g);
  int parse_cmd_line(char * x);
  int single_weave_count;
  vector<int> vector_single_weave_count;
  int weave_count;
  int single_bang_count;
  vector<int> vector_single_bang_count;
  int single_pre_prune_bang_count;
  int single_post_prune_bang_count;
  vector<int> vector_single_pre_prune_bang_count;
  vector<int> vector_single_post_prune_bang_count;
  int bang_count;
  int backtrack_count;
  int backtrack_success;
  bool backtrack_flag;
  int prune_count;
  int clump_prune_count;
  int context_count;
  int merge_count;
  int bang_count_in_merge;
  bool search_location(char * w, Location ** m);
  bool search_transition_relation(char * w, TransitionRelation ** m);
  int find_variable( char* what);
  void add_preloc_invariants_to_transitions();
  void print_status();
  void print_bake_off(InvariantMap const & what);
   
  void check_invariant_ok();
   
%}

%union{
   char * string;
   var_info * v;
   int dummy;
   int integer;
   char identifier[MAX_ID_SIZE];
   var_info * vi;
   Location *ll;
   TransitionRelation * tt;
   Linear_Expression * li;
   Constraint * cc;
   C_Polyhedron * pp;
   vector<int> * vv;
}


%token <integer> INT
%token <identifier> IDENT
%token PRIME END VARIABLED LOCATION TRANSITION
%token EQ LEQ GEQ LE GE
%token PRES PROPS INVARIANT

%type<vi> dimvector
%type<identifier> identifier
%type<ll> location_identifier location_descriptor
%type<tt> transition_identifier transition_descriptor
%type<li> linear_expression primed_linear_expression linear_term primed_term
%type<cc> linear_inequality primed_linear_inequality
%type<pp> linear_assertion primed_linear_assertion preservative
%type<vv> variable_list


%start program

%nonassoc GEQ LEQ EQ
%left '+' '-'
%left '*'
%right UMINUS


%%

program: header optional_commands system_descriptor END{
   // just print it for the fun of it
};

header: VARIABLED {
} '[' dimvector ']'{
   f=$4; // This is the main dimvector
   dimension=f->get_dimension();
}
;

optional_commands: PROPS '(' INT ')' {
   prop_steps=$3;
   
} | {}
;

dimvector: dimvector identifier {
   $$=$1;
   $$->search_and_insert($2);
}
| identifier {
   $$=new var_info();
   $$->search_and_insert($1);
};

system_descriptor:location_descriptor system_descriptor{
   
}
| transition_descriptor system_descriptor{

}
| location_descriptor{

}
| transition_descriptor{
   
}
| invariant_descriptor system_descriptor{}
| invariant_descriptor{}
;

location_descriptor: LOCATION location_identifier{
   $$=$2;
}
| LOCATION location_identifier linear_assertion{
   $$=$2;
   $$->set_polyhedron($3);
}
;

transition_descriptor: TRANSITION transition_identifier ':' location_identifier ',' location_identifier ',' primed_linear_assertion{
   $$=$2;
   $$->set_locs($4,$6);
   $$->set_relation($8);
}
| TRANSITION  transition_identifier ':' location_identifier ',' primed_linear_assertion{
   $$=$2;
   $$->set_locs($4,$4);
   $$->set_relation($6);
}
;

invariant_descriptor: INVARIANT location_identifier linear_assertion {
   $2->set_invariant_polyhedron($3);
}
| INVARIANT location_identifier ':' linear_assertion{
     $2->set_invariant_polyhedron($4);
}
;


location_identifier: identifier{
   // search loclist for the identifier
   Location * what;
   if (!search_location($1, &what)){
      $$=new Location(dimension,f,fd,fm,$1);
      loclist->push_back($$);
   } else
      $$=what;
}
;

transition_identifier: identifier{
      // search loclist for the identifier
   TransitionRelation * what;
   if (!search_transition_relation($1, &what)){
      $$=new TransitionRelation(dimension,f,fd,fm,$1);
      trlist->push_back($$);
   } else {
      cout<<"Error: Already Encountered transition name #"<<what<<$1;
      $$=what;
   }
};

linear_assertion: linear_inequality linear_assertion{
   $$=$2;
   //$$->add_constraint_and_minimize(*$1);
   $$->add_constraint(*$1);
   delete($1);
}
| linear_inequality{
   $$= new C_Polyhedron(dimension, UNIVERSE);
   //$$->add_constraint_and_minimize(*$1);
   $$->add_constraint(*$1);
   delete($1);
};

linear_inequality:  linear_expression LEQ linear_expression{
   $$=new Constraint(*$1 <= *$3);
   delete($1);
   delete($3);
}
|  linear_expression GEQ linear_expression{
   $$=new Constraint(*$1 >= *$3);
   delete($1);
   delete($3);
}
|  linear_expression EQ linear_expression{
   $$=new Constraint(*$1 == *$3);
   delete($1);
   delete($3);
   };

linear_term: identifier {
   int i =f->search($1);
   if (i==VAR_NOT_FOUND){
      string x=string("Error:: Variable ")+ $1 + string(" not found");
      yyerror(x);
      exit(1);
   }
   $$=new Linear_Expression(Variable(i));
}
| INT {
   $$= new Linear_Expression($1);
}
| INT '*' identifier{
   int i =f->search($3);
   if (i==VAR_NOT_FOUND){
      string x=string("Error:: Variable ")+ $3 + string(" not found");
      yyerror(x);
      exit(1);
   }
   $$=new Linear_Expression($1 * Variable(i));
};

linear_expression: linear_term{
   $$=$1;
}
| linear_expression '+' linear_term {
   $$=$1;
   (*$1)+=(*$3);
   delete($3);
   
}
| linear_expression '-' linear_term {
   $$=$1;
   (*$1)-=(*$3);
   delete($3);
}
| '-' linear_term %prec UMINUS{
   $$=$2;
   (*$2)=-(*$2);
}
;

primed_linear_assertion: primed_linear_inequality primed_linear_assertion{
   $$=$2;
   //$$->add_constraint_and_minimize(*$1);
   $$->add_constraint(*$1);
   delete($1);
}
| primed_linear_inequality{
   $$= new C_Polyhedron(2*dimension,UNIVERSE);
   //$$->add_constraint_and_minimize(*$1);
   $$->add_constraint(*$1);
   delete($1);
}
| preservative{
   $$=$1;
}
| preservative primed_linear_assertion{
   $$=$2;
   $$->intersection_assign(*$1);
   delete($1);
}
;

preservative: PRES '[' variable_list ']'{
   $$= new C_Polyhedron(2*dimension,UNIVERSE);
   vector<int>::iterator vi=$3->begin();
   for (; vi < $3->end(); ++vi){
      Linear_Expression ll=Variable((*vi)) - Variable((*vi)+dimension);
      //$$->add_constraint_and_minimize(ll ==0);
      $$->add_constraint(ll ==0);
   }

   delete($3);
   
}
;

variable_list: identifier variable_list {
   int i=find_variable($1);
   $$=$2;
   $$->push_back(i);
}
| identifier ',' variable_list {
   int i=find_variable($1);
   $$=$3;
   $$->push_back(i);
}
| identifier{
   int i=find_variable($1);
   $$=new vector<int>();
   $$->push_back(i);
}
;
primed_linear_inequality: primed_linear_expression LEQ primed_linear_expression{
   $$=new Constraint(*$1 <= *$3);
   delete($1);
   delete($3);
}
| primed_linear_expression EQ primed_linear_expression {
   $$=new Constraint(*$1== *$3);
   delete($1);
   delete($3);
}
| primed_linear_expression GEQ primed_linear_expression {
   $$= new Constraint(*$1 >= *$3);
   delete($1);
   delete($3);
};

primed_term: identifier {
   int i= find_variable($1);
   $$=new Linear_Expression(Variable(i));
}
| PRIME identifier{
   int i= find_variable($2);
   $$=new Linear_Expression(Variable(i+dimension));
}
| INT {
   $$=new Linear_Expression($1);
}
| INT '*' identifier{
   int i= find_variable($3);
   $$=new Linear_Expression($1 * Variable(i));
}
| INT '*' PRIME identifier{
   int i= find_variable($4);
   $$=new Linear_Expression($1 * Variable(i+dimension));
};

primed_linear_expression: primed_term{
   $$=$1;
}
| primed_linear_expression '+' primed_term{
   $$=$1;
   (*$1)+= (*$3);
   delete($3);
}

| primed_linear_expression '-' primed_term {
   $$=$1;
   (*$1)-= (*$3);
   delete($3);
}
| '-' primed_term %prec UMINUS{
   $$=$2;
   (*$2)= -(*$2);
}
;

identifier: IDENT{
  strcpy($$,$1);
}
;


%%

void do_some_propagation(){
   // try and fire each transition relation

   
   vector<TransitionRelation*>::iterator vi;
   int fired_up=0;
   int ntrans=trlist->size();


   while (fired_up < prop_steps * ntrans){
      for (vi=trlist->begin();vi < trlist->end(); vi++){
         (*vi)->fire();
         fired_up++;
      }
   }

}

int find_variable(char * what){
   int i=f->search(what);
   if (i==VAR_NOT_FOUND){
      string x=string("Error:: Variable ")+ what + string(" not found");
      yyerror(x);
      exit(1);
   }

   return i;
}

bool search_location( char * name, Location ** what){
   vector<Location*>::iterator vi;
   string nstr(name);
   for(vi=loclist->begin();vi< loclist->end();vi++){
      if ((*vi)->matches(nstr)){
         *what=(*vi);
         return true;
      }
   }

   return false;
}


bool search_transition_relation( char * name, TransitionRelation ** what){
   vector<TransitionRelation*>::iterator vi;
   string nstr(name);
   for(vi=trlist->begin();vi< trlist->end();vi++){
      if ((*vi)->matches(nstr)){
         *what=(*vi);
         return true;
      }
   }
   
   return false;
}

void yyerror(char const * x){
   yyerror(string(x));
}

void yyerror(string const & x){

   cerr<<x<<endl;
   cerr<<"Line number::"<<linenum<<endl;
   exit(1);
   
}

int parse_cmd_line(char * x){
   
   if (strcmp(x,"one")==0) return ONECONTEXT;
   if (strcmp(x,"many")==0) return MANYCONTEXT;
   if (strcmp(x,"new_many")==0) return NEW_MANYCONTEXT;
   if (strcmp(x,"new_2_many")==0) return NEW_2_MANYCONTEXT;
   if (strcmp(x,"new_3_many")==0) return NEW_3_MANYCONTEXT;
   if (strcmp(x,"newdfs")==0) return NEWDFS;
   if (strcmp(x,"newdfs_sequences")==0) return NEWDFS_SEQUENCES;
   if (strcmp(x,"noProjection")==0) return NO_PROJECTION;
   if (strcmp(x,"FEC")==0) return FARKAS_ELIMINATE_C;
   if (strcmp(x,"KEC")==0) return KOHLER_ELIMINATE_C;
   if (strcmp(x,"REC")==0) return FOUMOT_ELIMINATE_C;
   if (strcmp(x,"no_prior")==0) return NO_PRIOR;
   if (strcmp(x,"target_prior1")==0) return TARGET_PRIOR1;
   if (strcmp(x,"target_prior2")==0) return TARGET_PRIOR2;
   if (strcmp(x,"target_prior3")==0) return TARGET_PRIOR3;
   if (strcmp(x,"one_per_group")==0) return ONE_PER_GROUP;
   if (strcmp(x,"two_per_group")==0) return TWO_PER_GROUP;
   if (strcmp(x,"three_per_group")==0) return THREE_PER_GROUP;
   if (strcmp(x,"four_per_group")==0) return FOUR_PER_GROUP;
   if (strcmp(x,"gendrop")==0) return GENDROP;
   if (strcmp(x,"zero_only")==0) return ZERO_ONLY;
   if (strcmp(x,"one_only")==0) return ONE_ONLY;
   if (strcmp(x,"zero_one")==0) return ZERO_ONE;
   if (strcmp(x,"noinst")==0) return NO_INSTANTIATION;
   if (strcmp(x,"noch79")==0) return NO_CH79;
   if (strcmp(x,"nobhrz03")==0) return NO_BHRZ03;
   if (strcmp(x,"dual")==0) return YES_DUAL;
   if (strcmp(x,"ch79")==0) return YES_CH79;
   if (strcmp(x,"bhrz03")==0) return YES_BHRZ03;
   if (strcmp(x,"nodual")==0) return NO_DUAL;
   if (strcmp(x,"invcheck")==0) return INV_CHECK;
   if (strcmp(x,"noinvcheck")==0) return NO_INV_CHECK;
   
  
   return BULLSHIT;
}
void Print_Location();
void collect_invariants(C_Polyhedron & cpoly, C_Polyhedron & invd){
  /*
   *  Collect invariants
   */
  vector<Location * >::iterator vl;
  invd=C_Polyhedron(fd->get_dimension(),UNIVERSE);
  vl = loclist->begin();
  //cout<<endl<<"- In collect_invariants(), cpoly is : "<<endl<<"  "<<cpoly<<endl;
  //Generator_System mgs = cpoly.minimized_generators();
  for (vl=loclist->begin();vl<loclist->end();vl++){
    (*vl)->extract_invariants_and_update(cpoly,invd);
    //(*vl)->extract_invariant_from_generator(mgs);
    //(*vl)->update_dual_constraints(invd);
    //cout<<endl<<"5.";
    //Print_Location();
  }
  return;
}

void collect_invariants_for_initial_by_eliminating(C_Polyhedron & cpoly, C_Polyhedron & invd){
  //
  //  Collect invariants for initial
  //
  vector<Location * >::iterator vl;
  invd=C_Polyhedron(fd->get_dimension(),UNIVERSE);
  vl = loclist->begin();

  //    Firstly, collect invariants for initial location by eliminating
  //      for initial *vl, i.e. location, 
  //      use cpoly to update *vl->invariant and *vl->invariant updates invd.
  //for (vl=loclist->begin(); vl!=loclist->end(); vl++)
  (*vl)->extract_invariants_and_update_for_one_location_by_eliminating(cpoly,invd);
  /*
  //  Recursive Propagation
  //    Secondly, build the invariants from initial location by propagation
  int propagation_flag[location_count]={0};
  propagation_flag[0]=1;
  int i = 0;
  for ( vl = loclist->begin(); vl < loclist->end(); vl++ ){// propagate from i-th location
    for (int j=0; j<location_count; j++){
      if (propagation_flag[j] == 0){// the location without invariants needs to propagate
        if ( !location_matrix[i][j].empty() ){// find the non-empty vector of location_matrix
          cout<<endl<<"Location "<<(*loclist)[j]->get_name()<<" at Propagation:";
          //  prepare the consatraints
          C_Polyhedron loc_i_inv = (*loclist)[i]->get_invariant();
          int trans_index = location_matrix[i][j][0];
          C_Polyhedron trans_relation = (*trlist)[trans_index]->get_relation();
          cout<<endl<<"From Location invariant "<<(*loclist)[i]->get_name()<<endl<<"   "<<loc_i_inv;
          cout<<endl<<"Through Transition relation "<<(*trlist)[trans_index]->get_name()<<": "<<endl<<"   "<<trans_relation;

          //  Propagation
          (*loclist)[j]->propagate_invariants_and_update_for_except_initial_by_propagation(loc_i_inv, trans_relation);
          //    Contains Test
          (*loclist)[j]->contains_test(cpoly, loc_i_inv, trans_relation);

          //  make flag for location has been added invariants
          propagation_flag[j]=1;
        }
      }
    }
    i++;
  }
  */
  return;
}

void collect_invariants_for_except_initial_by_propagation(){
  //
  //  Collect invariants for except initial
  //
  vector<Location * >::iterator vl;

  //    Secondly, build the invariants from initial location by propagation
  int propagation_flag[location_count]={0};
  propagation_flag[0]=1;
  int i = 0;
  for ( vl = loclist->begin(); vl < loclist->end(); vl++ ){// propagate from i-th location
    //  The "int i" is the index of loclist,
    //  we just use vl = loclist->begin() to count for intuition
    //  but actually use "int i" to count in following index
    for (int j=0; j<location_count; j++){
      if (propagation_flag[j] == 0){// the location without invariants needs to propagate
        if ( !location_matrix[i][j].empty() ){// find the non-empty vector of location_matrix
          cout<<endl<<"Location "<<(*loclist)[j]->get_name()<<" at Propagation:";
          
          //  prepare the constraints for location invariant and transition relation
          C_Polyhedron loc_i_inv = (*loclist)[i]->get_invariant();
          for (vector<int>::iterator trans_index=location_matrix[i][j].begin(); trans_index<location_matrix[i][j].end(); trans_index++){
            C_Polyhedron trans_relation = (*trlist)[*trans_index]->get_relation();
            cout<<endl<<"From Location invariant "<<(*loclist)[i]->get_name()<<endl<<"   "<<loc_i_inv;
            cout<<endl<<"Through Transition relation "<<(*trlist)[*trans_index]->get_name()<<": "<<endl<<"   "<<trans_relation;

            //  Propagation
            (*loclist)[j]->propagate_invariants_and_update_for_except_initial_by_propagation(loc_i_inv, trans_relation);
            //    Contains Test
            //(*loclist)[j]->contains_test(cpoly, loc_i_inv, trans_relation);
          }
          /*
          int trans_index = location_matrix[i][j][0];
          C_Polyhedron trans_relation = (*trlist)[trans_index]->get_relation();
          cout<<endl<<"From Location invariant "<<(*loclist)[i]->get_name()<<endl<<"   "<<loc_i_inv;
          cout<<endl<<"Through Transition relation "<<(*trlist)[trans_index]->get_name()<<": "<<endl<<"   "<<trans_relation;

          //  Propagation
          (*loclist)[j]->propagate_invariants_and_update_for_except_initial_by_propagation(loc_i_inv, trans_relation);
          //    Contains Test
          //(*loclist)[j]->contains_test(cpoly, loc_i_inv, trans_relation);
          */

          //  make flag for location has been added invariants
          propagation_flag[j]=1;
        }
      }
    }
    i++;
  }
  
  return;
}

void collect_invariants_for_initial_by_recursive_eliminating(C_Polyhedron & cpoly, C_Polyhedron & invd){
  /*
   *  Collect invariants
   */
  vector<Location * >::iterator vl;
  invd=C_Polyhedron(fd->get_dimension(),UNIVERSE);

  //    Firstly, collect invariants for initial location by recursive eliminating
  vl = loclist->begin();
  (*vl)->extract_invariants_and_update_for_initial_by_recursive_eliminating(cpoly,invd);

  return;
}

void collect_invariants_for_one_location_by_eliminating(int target_index, C_Polyhedron & cpoly, C_Polyhedron & invd){
  //
  //  Collect invariants for initial
  //
  invd=C_Polyhedron(fd->get_dimension(),UNIVERSE);
  //    Firstly, collect invariants for initial location by eliminating
  //      for initial *vl, i.e. location, 
  //      use cpoly to update *vl->invariant and *vl->invariant updates invd.
  (*loclist)[target_index]->extract_invariants_and_update_for_one_location_by_eliminating(cpoly,invd);

  return;
}

void binary_eliminating(C_Polyhedron & cpoly, C_Polyhedron & invd){
  //cout<<endl<<"7.get here?";
  cout<<endl<<"(int)(cpoly.space_dimension()) :"<<(int)(cpoly.space_dimension());
  cout<<endl<<"( (*loclist)[0]->get_dimension()+1 ) : "<<( (*loclist)[0]->get_dimension()+1);
  if ( (int)(cpoly.space_dimension()) == ( (*loclist)[0]->get_dimension()+1 ) ){
    //cout<<endl<<"8.get here?";
    (*loclist)[global_binary_i]->extract_invariants_and_update_by_binary_eliminating(cpoly, invd);
    global_binary_i++;
    cout<<endl<<"global_binary_i : "<<global_binary_i;
    return;
  }
  //cout<<endl<<"9.get here?";

  C_Polyhedron p_left = cpoly;
  C_Polyhedron p_right = cpoly;
  C_Polyhedron *cpoly_left = new C_Polyhedron(cpoly.space_dimension(), UNIVERSE); 
  *cpoly_left = p_left;
  C_Polyhedron *cpoly_right = new C_Polyhedron(cpoly.space_dimension(), UNIVERSE); 
  //*cpoly_right = swap2_index_and_divide_from(cpoly, cpoly.space_dimension()/2);
  *cpoly_right = p_right;
  //cout<<endl<<"1.get here?";

  int l = 0;
  int m = cpoly.space_dimension()/2;
  int h = cpoly.space_dimension();
  Project_by_Kohler(*cpoly_left, l, m);
  Project_by_Kohler(*cpoly_right, m, h);
  //cout<<endl<<"2.get here?";

  binary_eliminating(*cpoly_left, invd);
  //cout<<endl<<"3.get here?";
  delete(cpoly_left);
  //cout<<endl<<"4.get here?";
  binary_eliminating(*cpoly_right, invd);
  //cout<<endl<<"5.get here?";
  delete(cpoly_right);
  //cout<<endl<<"6.get here?";

  return;
}

void collect_invariants_by_binary_eliminating(C_Polyhedron & cpoly, C_Polyhedron & invd){
  /*
   *  Collect invariants
   */
  vector<Location * >::iterator vl;
  invd=C_Polyhedron(fd->get_dimension(),UNIVERSE);

  //    Firstly, collect invariants for initial location by recursive eliminating
  //vl = loclist->begin();
  //(*vl)->extract_invariants_and_update_for_initial_by_recursive_eliminating(cpoly,invd);
  
  binary_eliminating(cpoly, invd);
  global_binary_i=0;

  return;
}

void dfs_traverse_recursive(int depth, vector<Clump> & vcl, C_Polyhedron & cpoly, C_Polyhedron & invd){
   /*
   cout<<endl;
   cout<<endl<<"  "<<"depth "<<depth;
   cout<<endl<<"  "<<"invd is ";
   cout<<endl<<"    "<<invd;
   cout<<endl<<"  "<<"cpoly is ";
   cout<<endl<<"    "<<cpoly;
   cout<<endl<<"  "<<"invd contains cpoly ? ";
   */
  //cout<<endl<<"depth:"<<depth<<", cpoly:";
  //cout<<endl<<cpoly;

   if (invd.contains(cpoly)){
      bang_count++;
      //cout<<"banged";
      return;
   }
   
   if (depth==0){
      weave_count++;
      cout<<endl<<"/-----------------------------";
      collect_timer.restart();
      collect_invariants(cpoly,invd);
      cout<<endl<<"- Have Collected "<<weave_count<<" invariant(s) ";
      collect_timer.stop();
      cout<<endl<<"- The collect_invariants Time Taken (0.01s) = "<<collect_timer.compute_time_elapsed()<<endl;
      collect_time = collect_time + collect_timer.compute_time_elapsed();
      cout<<endl<<"\\-----------------------------"<<endl;
      //    prune_clumps(vcl);
      return;
   }

   if (weave_timer.compute_time_elapsed() >= weave_time){
      cout<< "Time is up!"<<endl;
      return;
   }
   
   vcl[depth-1].clear();
   while(vcl[depth-1].has_next()){
      //cout<<endl<<"in while...next()";
      //cout<<endl<<"depth:"<<depth<<", cpoly:";
      //cout<<endl<<cpoly;
      //cout<<endl<<"vcl["<<depth-1<<"].size():"<<vcl[depth-1].get_count();
      C_Polyhedron p(cpoly);
      //Timer test_time_for_intersection;
      p.intersection_assign(vcl[depth-1].get_reference());
      //test_time_for_intersection.stop();
      //cout<<endl<<"- Intersection Time Taken (0.01s) = "<<test_time_for_intersection.compute_time_elapsed()<<endl;

      dfs_traverse_recursive(depth-1,vcl,p,invd);

      vcl[depth-1].next();
   }
   return;
}

void dfs_traverse_recursive_for_initial_by_eliminating(int depth, vector<Clump> & vcl, C_Polyhedron & cpoly, C_Polyhedron & invd){
   if (invd.contains(cpoly)){
      bang_count++;
      return;
   }
   
   if (depth==0){
      weave_count++;
      cout<<endl<<"/-----------------------------";
      //Timer test_time_for_minimized;
      collect_invariants_for_initial_by_eliminating(cpoly,invd);
      cout<<endl<<"- Have Collected "<<weave_count<<" invariant(s)";
      //test_time_for_minimized.stop();
      //cout<<endl<<"- The collect_invariants's function Time Taken (0.01s) = "<<test_time_for_minimized.compute_time_elapsed()<<endl;
      cout<<endl<<"\\-----------------------------"<<endl;
      //    prune_clumps(vcl);
      return;
   }

   if (weave_timer.compute_time_elapsed() >= weave_time){
      cout<< "Time is up!"<<endl;
      return;
   }
   
   vcl[depth-1].clear();
   while(vcl[depth-1].has_next()){
      
      C_Polyhedron p(cpoly);
      //Timer test_time_for_intersection;
      p.intersection_assign(vcl[depth-1].get_reference());
      //test_time_for_intersection.stop();
      //cout<<endl<<"- Intersection Time Taken (0.01s) = "<<test_time_for_intersection.compute_time_elapsed()<<endl;

      dfs_traverse_recursive_for_initial_by_eliminating(depth-1,vcl,p,invd);

      vcl[depth-1].next();
   }
   return;
}

void dfs_traverse_recursive_for_initial_by_recursive_eliminating(int depth, vector<Clump> & vcl, C_Polyhedron & cpoly, C_Polyhedron & invd){
   
   if (invd.contains(cpoly)){
      bang_count++;
      return;
   }
   
   if (depth==0){
      weave_count++;
      cout<<endl<<"/-----------------------------";
      Timer test_time_for_minimized;
      collect_invariants_for_initial_by_recursive_eliminating(cpoly,invd);
      test_time_for_minimized.stop();
      cout<<endl<<"- The collect_invariants's function Time Taken (0.01s) = "<<test_time_for_minimized.compute_time_elapsed()<<endl;
      cout<<"\\-----------------------------"<<endl;
      //    prune_clumps(vcl);
      return;
   }

   if (weave_timer.compute_time_elapsed() >= weave_time){
      cout<< "Time is up!"<<endl;
      return;
   }
   
   vcl[depth-1].clear();
   while(vcl[depth-1].has_next()){
      
      C_Polyhedron p(cpoly);
      //Timer test_time_for_intersection;
      p.intersection_assign(vcl[depth-1].get_reference());
      //test_time_for_intersection.stop();
      //cout<<endl<<"- Intersection Time Taken (0.01s) = "<<test_time_for_intersection.compute_time_elapsed()<<endl;

      dfs_traverse_recursive_for_initial_by_recursive_eliminating(depth-1,vcl,p,invd);

      vcl[depth-1].next();
   }
   return;
}

void dfs_traverse_recursive_for_binary_eliminating(int depth, vector<Clump> & vcl, C_Polyhedron & cpoly, C_Polyhedron & invd){
   
   //Timer test_time_for_contains;
   int contains=invd.contains(cpoly);
   //test_time_for_contains.stop();
   //cout<<endl<<"- The contains function Time Taken (0.01s) = "<<test_time_for_contains.compute_time_elapsed();
   //global_contains_time+=test_time_for_contains.compute_time_elapsed();
   //cout<<endl<<"- The global_contains_time Time Taken (0.01s) = "<<global_contains_time;
   if (contains){
      bang_count++;
      return;
   }
   
   if (depth==0){
      weave_count++;
      cout<<endl<<"/-----------------------------";
      //Timer test_time_for_minimized;
      collect_invariants_by_binary_eliminating(cpoly,invd);
      cout<<endl<<"- Have Collected "<<weave_count<<" invariant(s) ";
      //test_time_for_minimized.stop();
      //cout<<endl<<"- The collect_invariants's function Time Taken (0.01s) = "<<test_time_for_minimized.compute_time_elapsed()<<endl;
      cout<<endl<<"\\-----------------------------"<<endl;
      //    prune_clumps(vcl);
      return;
   }

   if (weave_timer.compute_time_elapsed() >= weave_time){
      cout<< "Time is up!"<<endl;
      return;
   }
   
   vcl[depth-1].clear();
   while(vcl[depth-1].has_next()){
      
      C_Polyhedron p(cpoly);
      //Timer test_time_for_intersection;
      p.intersection_assign(vcl[depth-1].get_reference());
      //test_time_for_intersection.stop();
      //cout<<endl<<"- Intersection Time Taken (0.01s) = "<<test_time_for_intersection.compute_time_elapsed()<<endl;

      dfs_traverse_recursive_for_binary_eliminating(depth-1,vcl,p,invd);

      vcl[depth-1].next();
   }
   return;
}

void dfs_traverse_recursive_for_one_location_by_eliminating(int target_index, int depth, Tree & tr, C_Polyhedron & cpoly, C_Polyhedron & invd){

   if (invd.contains(cpoly)){
      //tr.Print_Prune_Tree(depth,"Banged"); // print for debug and improve algorithm
      bang_count++;
      single_bang_count++;
      return;
   }

   if (depth==0){
      //backtrack_flag = true;
      weave_count++;
      single_weave_count++;
      cout<<endl<<endl<<"/-----------------------------";
      tr.Print_Prune_Tree(depth,"Weaved"); // print for debug and improve algorithm
      collect_timer.restart();
      collect_invariants_for_one_location_by_eliminating(target_index, cpoly, invd);
      cout<<endl;
      cout<<endl<<"- Have Collected "<<weave_count<<" invariant(s)";
      collect_timer.stop();
      cout<<endl<<"- The collect_invariants Time Taken (0.01s) = "<<collect_timer.compute_time_elapsed();
      collect_time = collect_time + collect_timer.compute_time_elapsed();
      single_collect_time = single_collect_time + collect_timer.compute_time_elapsed();
      cout<<endl<<"\\-----------------------------"<<endl;
      prune_nodes_timer.restart();
      //tr.prune_node_self_inspection(target_index,invd);
      prune_nodes_timer.stop();
      prune_nodes_time += prune_nodes_timer.compute_time_elapsed();
      return;
   }

   if (total_time.compute_time_elapsed() >= weave_time){
      cout<< "Time is up!"<<endl;
      return;
   }
   
   tr.get_clump(depth-1).clear();
   while(tr.get_clump(depth-1).has_next()){
      
      C_Polyhedron p(cpoly);
      p.intersection_assign(tr.get_clump(depth-1).get_reference());

      dfs_traverse_recursive_for_one_location_by_eliminating(target_index,depth-1,tr,p,invd);
      
      backtrack_timer.restart(); // Timer On
      if (backtrack_flag == true){
        bool flag = invd.contains(cpoly);
        if (flag){
          backtrack_success++;
          cout<<endl<<"Pruned by backtracking in depth "<<depth;
          tr.get_clump(depth-1).clear();
          return;
        }
        else {
          if (backtrack_success >= 1){
            backtrack_count++;
            backtrack_success = 0;
          }
          backtrack_flag = false;
        }
      }
      backtrack_timer.stop(); // Timer Off
      backtrack_time += backtrack_timer.compute_time_elapsed();
      
      // For prune_node_self_inspection
      if (depth-1 < tr.get_first_conflict()){
        return;
      }
      else if (depth-1 == tr.get_first_conflict()){
        tr.clear_first_conflict();
        backhere_flag = true;
      }

      if (backhere_flag == false){
        tr.get_clump(depth-1).next();
      }
      else {
        backhere_flag = false;
      }
   }
   return;
}

void dfs_traverse(vector<Clump> & vcl, C_Polyhedron & initp){
   // first find out the number of clumps
   // a polyhedron containing the solutions contained to date
   // initiate a dfs traversal.
   // write an invariant extraction function at depth 0

   C_Polyhedron  invd(*trivial);
   int ncl=0;
   vector<Clump>::iterator vi;
   for (vi=vcl.begin();vi < vcl.end();vi++){
      ncl++;
      (*vi).clear();
   }

   weave_timer.restart();

   /***/
   // modified and needed be deleted
   //cout<<endl<<"test and set 'ncl'=? ";
   //ncl=0;
   //vector<Clump> test_vcl = vcl;
   //test_vcl[0] = vcl[3];
   /***/
  
   dfs_traverse_recursive(ncl,vcl,initp,invd);
   
}

void dfs_traverse_for_initial_by_eliminating(vector<Clump> & vcl, C_Polyhedron & initp){
  // Here is the function of "extract_invariant_by_eliminating()"
  C_Polyhedron  invd(*trivial);
  int ncl=0;
  vector<Clump>::iterator vi;
  for (vi=vcl.begin();vi < vcl.end();vi++){
      ncl++;
      (*vi).clear();
  }
  weave_timer.restart();

  dfs_traverse_recursive_for_initial_by_eliminating(ncl,vcl,initp,invd);
}

void dfs_traverse_for_initial_by_recursive_eliminating(vector<Clump> & vcl, C_Polyhedron & initp){
  // Here is the function of "extract_invariant_by_eliminating()"
  C_Polyhedron  invd(*trivial);
  int ncl=0;
  vector<Clump>::iterator vi;
  for (vi=vcl.begin();vi < vcl.end();vi++){
      ncl++;
      (*vi).clear();
  }
  weave_timer.restart();

  dfs_traverse_recursive_for_initial_by_recursive_eliminating(ncl,vcl,initp,invd);
}

void dfs_traverse_for_binary_eliminating(vector<Clump> & vcl, C_Polyhedron & initp){
  // Here is the function of "extract_invariant_by_eliminating()"
  C_Polyhedron  invd(*trivial);
  int ncl=0;
  vector<Clump>::iterator vi;
  for (vi=vcl.begin();vi < vcl.end();vi++){
      ncl++;
      (*vi).clear();
  }
  weave_timer.restart();

  dfs_traverse_recursive_for_binary_eliminating(ncl,vcl,initp,invd);
}

void dfs_traverse_for_one_location_by_eliminating(int target_index, vector<Clump> & vcl, C_Polyhedron & initp){
  C_Polyhedron invd(*trivial);
  Tree tr = Tree(); //empty tree
  tr.set_target_index(target_index);
  int ncl=0;
  vector<Clump>::iterator vi;
  for (vi=vcl.begin();vi < vcl.end();vi++){
      ncl++;
      (*vi).clear();
  }

  cout<<endl<<endl<<"/ Start to solve Location "<<(*loclist)[target_index]->get_name();
  if (tree_prior == "target_prior1"){
    cout<<endl<<"/ Using target_prior1";
    tr.Reorder_Target_Prior_1(vcl);
  }
  else if (tree_prior == "target_prior2"){
    cout<<endl<<"/ Using target_prior2";
    tr.Reorder_Target_Prior_2(vcl);
  }
  else if (tree_prior == "target_prior3"){
    cout<<endl<<"/ Using target_prior3";
    tr.Reorder_Target_Prior_3(vcl);
  }
  else {
    cout<<endl<<"Wrong Type: "<<tree_prior;
  }

  //tr.prune_clumps_by_hierarchy_inclusion();

  dfs_traverse_recursive_for_one_location_by_eliminating(target_index,ncl,tr,initp,invd);
}

void dfs_sequences_generation_traverse(vector<vector<vector<vector<int>>>> & target_sequences, int target_index, vector<Clump> & vcl, C_Polyhedron & initp){
  //C_Polyhedron invd(*trivial);
  Tree tr = Tree(); //empty tree
  tr.set_target_index(target_index);
  //int ncl=0;
  vector<Clump>::iterator vi;
  for (vi=vcl.begin();vi < vcl.end();vi++){
      //ncl++;
      (*vi).clear();
  }

  cout<<endl<<endl<<"/ Start to solve Location "<<(*loclist)[target_index]->get_name();
  if (tree_prior == "no_prior"){
    cout<<endl<<"/ Using no_prior";
    tr.Original_Prior(vcl);
  }
  else if (tree_prior == "target_prior1"){
    cout<<endl<<"/ Using target_prior1";
    tr.Reorder_Target_Prior_1(vcl);
  }
  else if (tree_prior == "target_prior2"){
    cout<<endl<<"/ Using target_prior2";
    tr.Reorder_Target_Prior_2(vcl);
  }
  else if (tree_prior == "target_prior3"){
    cout<<endl<<"/ Using target_prior3";
    tr.Reorder_Target_Prior_3(vcl);
  }
  else {
    cout<<endl<<"Wrong Type: "<<tree_prior;
  }

  //tr.prune_clumps_by_hierarchy_inclusion();
  //dfs_traverse_recursive_for_one_location_by_eliminating(target_index,ncl,tr,initp,invd);

  cout<<endl<<"/ Generate Sequences";
  vector<vector<vector<int>>> sequences;
  sequences = tr.sequences_generation(some_per_group, initp);
  target_sequences.push_back(sequences);

}

void dfs_sequences_traverse_for_one_location_by_eliminating(vector<vector<vector<int>>> sequences, int target_index, vector<Clump> & vcl, C_Polyhedron & initp){
  C_Polyhedron invd(*trivial);
  Tree tr = Tree(); //empty tree
  tr.set_target_index(target_index);
  //int ncl=0;
  vector<Clump>::iterator vi;
  for (vi=vcl.begin();vi < vcl.end();vi++){
      //ncl++;
      (*vi).clear();
  }

  cout<<endl<<endl<<"/ Start to solve Location "<<(*loclist)[target_index]->get_name();
  if (tree_prior == "no_prior"){
    cout<<endl<<"/ Using no_prior";
    tr.Original_Prior(vcl);
  }
  else if (tree_prior == "target_prior1"){
    cout<<endl<<"/ Using target_prior1";
    tr.Reorder_Target_Prior_1(vcl);
  }
  else if (tree_prior == "target_prior2"){
    cout<<endl<<"/ Using target_prior2";
    tr.Reorder_Target_Prior_2(vcl);
  }
  else if (tree_prior == "target_prior3"){
    cout<<endl<<"/ Using target_prior3";
    tr.Reorder_Target_Prior_3(vcl);
  }
  else {
    cout<<endl<<"Wrong Type: "<<tree_prior;
  }

  //tr.prune_clumps_by_hierarchy_inclusion();
  //dfs_traverse_recursive_for_one_location_by_eliminating(target_index,ncl,tr,initp,invd);

  //cout<<endl;
  cout<<endl<<"/ Read(Traverse) Sequences";
  tr.dfs_sequences_traverse(sequences, initp, invd);
}

void Initialize_before_Parser(){

  cout<<endl<<"- Initialize_before_Parser doing...";
   weave_count=bang_count=backtrack_count=0;
   backtrack_success = 0;
   backtrack_flag = false;
   merge_count = 0;
   linenum=0;
   inv_check=false;
   clump_prune_count=prune_count=0;
   context_count=0;
   fm=new var_info();
   fd=new var_info();
   loclist= new vector<Location *>();
   trlist=new vector<TransitionRelation *>();
   num_context=2;
   projection = "kohler_improvement_eliminate_c";
   tree_prior = "target_prior2";
   some_per_group="two_per_group";
   gendrop=false;
   global_sub_system_list=new vector<System *> ();
   zero=one=true;
   prop_steps=2;
   weave_time=3600000;
   ch79=false;
   bhrz03=false;
   dual=false;
  cout<<"Done!"<<endl;
}

void Scan_Input(int argc, char * argv[]){
  cout<<endl<<"- Scan_Input doing...";

  // print argc and argc
  cout<<endl<<"argc: "<<argc<<endl;
  for (int i = 0; i < argc; i++){
    cout<<"argv: "<<argv[i]<<endl;
  }

  if (argc<=1){
    // by default one context and no gendrop
    num_context=2;
    projection = "kohler_improvement_eliminate_c";
    tree_prior = "target_prior2";
    some_per_group="two_per_group";
    gendrop=false;
  } else {
    for (int k=1;k<argc;k++){
      switch(parse_cmd_line(argv[k])){
        case GENDROP:
          gendrop=true;
          break;
        case ONECONTEXT: //Option: one
          num_context=1;
          break;
        case MANYCONTEXT: //Option: many
          num_context=2;
          break;
        case NEW_MANYCONTEXT: //Option: new method for many, eliminate C
          num_context=3;
          break;
        case NEW_2_MANYCONTEXT: //Option: new method for many, recursive eliminate
          num_context=4;
          break;
        case NEW_3_MANYCONTEXT:
          num_context=5;
          break;
        case NEWDFS:
          num_context=6;
          break;
        case NEWDFS_SEQUENCES:
          num_context=7;
          break;
        case NO_PROJECTION:
          projection = "no_projection";
          break;
        case KOHLER_ELIMINATE_C:
          projection = "kohler_improvement_eliminate_c";
          break;
        case FARKAS_ELIMINATE_C:
          projection = "farkas_eliminate_c";
          break;
        case FOUMOT_ELIMINATE_C:
          projection = "foumot_eliminate_c";
          break;
        case NO_PRIOR:
          tree_prior = "no_prior";
          break;
        case TARGET_PRIOR1:
          tree_prior = "target_prior1";
          break;
        case TARGET_PRIOR2:
          tree_prior = "target_prior2";
          break;
        case TARGET_PRIOR3:
          tree_prior = "target_prior3";
          break;
        case ONE_PER_GROUP:
          some_per_group="one_per_group";
          break;
        case TWO_PER_GROUP:
          some_per_group="two_per_group";
          break;
        case THREE_PER_GROUP:
          some_per_group="three_per_group";
          break;
        case FOUR_PER_GROUP:
          some_per_group="four_per_group";
          break;
        case ZERO_ONLY:
          one=false;
          zero=true;
          break;
        case ONE_ONLY:
          one=true;
          zero=false;
          break;
        case ZERO_ONE:
          zero=one=true;
          break;

        case NO_INSTANTIATION:
          zero=one=false;
          break;
        case NO_CH79: //Option: noch79(on): Do not do ch79
          ch79=false;
          break;
        case YES_CH79:
          ch79=true;
          break;

        case NO_BHRZ03: //Option: nobhrz03(on): Do not do bhrz03
          bhrz03=false;
          break;
        case YES_BHRZ03:
          bhrz03=true;
          break;

        case NO_DUAL:
          dual=false;
          break;
        case YES_DUAL:
          dual=true;
          break;
        case INV_CHECK:
          inv_check=true;
          break;
        case NO_INV_CHECK:
          inv_check=false;
          break;
        default:
          cerr<<"Illegal option:"<<argv[k]<<" ignored."<<endl;
          cerr<<"Usage:"<<argv[0]<<" [one,many,dual,nodual,ch79,noch79,bhrz03,nobhrz03,invcheck,noinvcheck] [ < input file ] [> output file ] "<<endl;
          break;
      }
    }
  }
  cout<<"Done!"<<endl;
}

void Print_Location_and_Transition(){
   cout<<endl;
   cout<<"----------------------------- "<<endl;
   cout<<"| The Locations read in are: "<<endl;
   cout<<"----------------------------- "<<endl;
   for (vector<Location *>::iterator vi=loclist->begin();vi< loclist->end();vi++){
      cout<<*(*vi);
   }
   cout<<"----------------------------- "<<endl;
   cout<<"| The Transitions read in are: "<<endl;
   cout<<"----------------------------- "<<endl;
   for (vector<TransitionRelation *>::iterator vj=trlist->begin();vj< trlist->end();vj++){
      cout<<*(*vj);
   }
}

void Print_Location(){
   cout<<endl;
   cout<<"----------------------------- "<<endl;
   cout<<"| The Locations read in are: "<<endl;
   cout<<"----------------------------- "<<endl;
   for (vector<Location *>::iterator vi=loclist->begin();vi< loclist->end();vi++){
      cout<<*(*vi);
   }
}

void Print_Status_before_Solver(){
  cout<<endl;
  cout<<"/----------------------------- "<<endl;
  cout<<"| Status before Solver: "<<endl;
  cout<<"----------------------------- "<<endl;
  cout<<"| Strategy ID # "<<num_context<<endl;
  cout<<"| Strategy name : ";
  switch(num_context){
    case 1:cout<<"one"<<endl;break;
    case 2:cout<<"many"<<endl;break;
    case 6:cout<<"newdfs"<<endl;break;
    case 7:cout<<"newdfs_sequences"<<endl;break;
  }

  if (num_context == 6){

    cout<<"| DFS Search method : "<<tree_prior<<endl;
    cout<<"| Projection method : "<<projection<<endl;
  }

  if (num_context == 7){

    cout<<"| DFS Search method : "<<tree_prior<<endl;
    cout<<"| Sequences Divide method : "<<some_per_group<<endl;
    cout<<"| Projection method : "<<projection<<endl;
  }

  cout<<"| Local invariants to be generated : "<<zero<<endl;
  cout<<"| Increasing invariants to be generated : "<<one<<endl;
  cout<<"| Weave time allowed : "<<weave_time<<endl;
  cout<<"\\----------------------------- "<<endl;
}

void Print_Status_after_Solver(){
  cout<<endl;
  cout<<"/----------------------------- "<<endl;
  cout<<"| Status after Solver: "<<endl;
  cout<<"----------------------------- "<<endl;
  cout<<"| Time Taken Unit: (0.01s)"<<endl;
  cout<<"| # of Contexts generated = "<<context_count<<endl;
  cout<<"|"<<endl;
  cout<<"| # of pruned vcl in intra-transition = "<<prune_count<<endl;
  cout<<"| # of pruned nodes by self inspection = "<<clump_prune_count<<", Time = "<<prune_nodes_time<<endl;
  cout<<"| # of pruned by backtracking = "<<backtrack_count<<", Time = "<<backtrack_time<<endl;
  cout<<"| # of merged for sub sequences = "<<merge_count<<endl;
  cout<<"|"<<endl;
  cout<<"| t: collect_invariant Time"<<endl;
  cout<<"| w: invariants *weav*ed"<<endl;
  for (vector<int>::size_type i = 0; i < vector_single_collect_time.size(); ++i){
    cout<<"| LOC "<<i<<": t = "<<vector_single_collect_time[i]<<", w = "<<vector_single_weave_count[i]<<endl;
  }
  cout<<"| TOTAL: t = "<<collect_time<<", w = "<<weave_count<<endl;
  cout<<"|"<<endl;
  cout<<"| t: dfs_traverse Time"<<endl;
  cout<<"| b: path *bang*ed"<<endl;
  if (num_context != 1){
    for (vector<int>::size_type i = 0; i < vector_single_dfs_traverse_time.size(); ++i){
      cout<<"| LOC_"<<i<<": t = "<<vector_single_dfs_traverse_time[i]<<", b = "<<vector_single_bang_count[i]<<endl;
    }
    for (vector<int>::size_type i = 0; i < vector_single_pre_prune_bang_count.size(); ++i){
      cout<<"| PRE_"<<i<<": t = "<<vector_single_dfs_sequences_generation_time[i]<<", b = "<<vector_single_pre_prune_bang_count[i]<<endl;
    }
    for (vector<int>::size_type i = 0; i < vector_single_post_prune_bang_count.size(); ++i){
      cout<<"| PST_"<<i<<": t = "<<vector_single_dfs_sequences_traverse_time[i]<<", b = "<<vector_single_post_prune_bang_count[i]<<endl;
    }
    cout<<"| TOTAL: t = "<<dfs_traverse_time<<", b = "<<bang_count<<endl;
  }
  cout<<"|"<<endl;
  cout<<"| TOTAL Time = "<<total_time.compute_time_elapsed()<<endl;
  cout<<"\\----------------------------- "<<endl;
}

int Get_Index_of_Location(string preloc_name){
  int i=0;
  for (vector<Location *>::iterator vi=loclist->begin();vi< loclist->end();vi++){
    if ((*vi)->get_name() == preloc_name){
      return i;
    }
    i++;
  }
}

int Get_Index_of_Transition(string name){
  int i=0;
  for (vector<TransitionRelation *>::iterator vi=trlist->begin();vi< trlist->end();vi++){
    if ((*vi)->get_name() == name){
      return i;
    }
    i++;
  }
}

void Create_Adjacency_Matrix_for_Location_and_Transition(){
  //  matrix initialization
  //    count the number of locations, i.e. length of matrix
  for (vector<Location *>::iterator vi=loclist->begin();vi< loclist->end();vi++){
    location_count++;
  }
  //    count the number of transitions and push back to the vector
  //vector<int> location_matrix[location_count][location_count];
  location_matrix = new vector<int>*[location_count];
  for (int i=0; i<location_count; i++){
    location_matrix[i] = new vector<int>[location_count];
  }

  int j=0;
  for (vector<TransitionRelation *>::iterator vj=trlist->begin();vj< trlist->end();vj++){
    location_matrix[Get_Index_of_Location((*vj)->get_preloc_name())][Get_Index_of_Location((*vj)->get_postloc_name())].push_back(j);
    j++;
  }

  //  print the matrix
  cout<<endl;
  cout<<"/----------------------------- "<<endl;
  cout<<"| Adjacency Matrix for Location and Transition: "<<endl;
  cout<<"----------------------------- "<<endl;
  cout<<"| [#] is transition_index"<<endl;
  for (int i=0; i<location_count; i++){
    cout<<"| "<<(*loclist)[i]->get_name()<<": ";
    for (int j=0; j<location_count; j++){
      cout<<"[";
      for (vector<int>::iterator it=location_matrix[i][j].begin(); it<location_matrix[i][j].end(); it++){
        cout<<" "<< *it <<" ";
      }
      cout<<"]->"<<(*loclist)[j]->get_name()<<";  ";
    }
    cout<<endl;
  }
  cout<<"\\----------------------------- "<<endl;
}

void Clear_Location_Invariant(){
  for (vector<Location * >::iterator vl=loclist->begin();vl<loclist->end();vl++){
    cout<<endl<<"- Location "<<(*vl)->get_name()<<": initialize invariant";
    (*vl)->initialize_invariant();
  }
}

int main(int argc, char * argv[]){
  ios::sync_with_stdio(false);
  total_time.restart();
  Initialize_before_Parser();  
  Scan_Input(argc, argv);
  cout<<endl<<"- Is yacc parsing done? "<<yyparse()<<endl;
  Print_Status_before_Solver();
  Print_Location_and_Transition();
  Create_Adjacency_Matrix_for_Location_and_Transition();
  
  add_preloc_invariants_to_transitions();
  global_system = new System(f, fd, fm);
  for (vector<Location *>::iterator vi = loclist->begin(); vi< loclist->end(); vi++){
    global_system->add_location((*vi));  
  }
  for (vector<TransitionRelation *>::iterator vj = trlist->begin(); vj< trlist->end(); vj++){
    global_system->add_transition((*vj));
  }
  global_system->compute_duals();
  tt = new int[fm->get_dimension()];

  if (num_context == 1){
    //  Implementation for Convert_CNF_to_DNF_and_Print() function
    //    due to num_context == 1, 
    //    i.e. intra-location / single-location

    glc = global_system->get_context();
    //Print_Location_and_Transition();
    trivial = new C_Polyhedron(fd->get_dimension(),UNIVERSE);
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_to_trivial(trivial);
    }
    invd = new C_Polyhedron(*trivial);
    cout<<endl;
    //cout<<"- The Convert_CNF_to_DNF_and_Print(): "<<endl;
    //cout<<"- The Root Context: "<<endl<<(*glc)<<endl;
    glc->Convert_CNF_to_DNF_and_Print(loclist, invd, weave_time, true);
  } // if (num_context == 1)
  else if (num_context == 2){
    //  Implementation for Eliminate_c_through_inter_Location() function
    //  compared with num_context == 3, here is no elimination.
    //    due to num_context == 2, 
    //    i.e. inter-location / many-locations
    //  output_file: **many**

    //    dualize using a clump
    int nd = fd->get_dimension();
    //    obtain a polyhedron characterizing "trivial"
    trivial = new C_Polyhedron(nd, UNIVERSE);
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_to_trivial(trivial); // Later, use this "trivial" to build (initial) "invd"
    }
    //    now dualize each location
    C_Polyhedron initp(nd, UNIVERSE); // for the dualized initial conditions
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->make_context();
      (*vi)->compute_dual_constraints(initp); // Later, use this "initp" to build (initial) "cpoly"
    }

    //    now dualize the transition systems and collect the "clumps"
    vector<Clump> vcl;
    for (vector<TransitionRelation *>::iterator vj = trlist->begin(); vj < trlist->end(); vj++){
      (*vj)->compute_consecution_constraints(vcl, initp);
    }
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_clump(vcl);
      //    this also should trigger the simplification of the context
    }
    dfs_traverse_timer.restart();
    dfs_traverse(vcl, initp);
    dfs_traverse_timer.stop();
    dfs_traverse_time = dfs_traverse_timer.compute_time_elapsed();
  } //    else if (num_context == 2)
  else if (num_context == 3){
    //  Implementation for Eliminate_c_through_inter_Location() function
    //  compared with num_context == 2, here is elimination!
    //    due to num_context == 3, 
    //    i.e. inter-location / many-locations
    //  output_file: **new_many**

    //    dualize using a clump
    int nd = fd->get_dimension();
    //    obtain a polyhedron characterizing "trivial"
    trivial = new C_Polyhedron(nd, UNIVERSE);
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_to_trivial(trivial);
    }
    //    now dualize each location
    C_Polyhedron initp(nd, UNIVERSE); // for the dualized initial conditions
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->make_context();
      (*vi)->compute_dual_constraints(initp);
    }

    //    now dualize the transition systems and collect the "clumps"
    vector<Clump> vcl;
    for (vector<TransitionRelation *>::iterator vj = trlist->begin(); vj < trlist->end(); vj++){
      (*vj)->compute_consecution_constraints(vcl, initp);
    }
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_clump(vcl);
      //    this also should trigger the simplification of the context
    }

    dfs_traverse_timer.restart();
    dfs_traverse_for_initial_by_eliminating(vcl, initp);
    //collect_invariants_for_except_initial_by_propagation();
    dfs_traverse_timer.stop();
    dfs_traverse_time = dfs_traverse_timer.compute_time_elapsed();

  } //    else if (num_context == 3)
  else if (num_context == 4){
    //  Implementation for Recursive_Eliminate_c_through_inter_Location() function
    //  compared with num_context == 3, here is recursive elimination!
    //    due to num_context == 4, 
    //    i.e. inter-location / many-locations
    //  output_file: **new_2_many**

    //    dualize using a clump
    int nd = fd->get_dimension();
    //    obtain a polyhedron characterizing "trivial"
    trivial = new C_Polyhedron(nd, UNIVERSE);
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_to_trivial(trivial);
    }
    //    now dualize each location
    C_Polyhedron initp(nd, UNIVERSE); // for the dualized initial conditions
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->make_context();
      (*vi)->compute_dual_constraints(initp);
    }

    //    now dualize the transition systems and collect the "clumps"
    vector<Clump> vcl;
    for (vector<TransitionRelation *>::iterator vj = trlist->begin(); vj < trlist->end(); vj++){
      (*vj)->compute_consecution_constraints(vcl, initp);
    }
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_clump(vcl);
      //    this also should trigger the simplification of the context
    }
    //  Here is the function of "extract_invariant_by_eliminating()"
    dfs_traverse_timer.restart();
    dfs_traverse_for_initial_by_recursive_eliminating(vcl, initp);
    dfs_traverse_timer.stop();
    dfs_traverse_time = dfs_traverse_timer.compute_time_elapsed();

  }//    else if (num_context == 4)
  else if (num_context == 5){
    //  Implementation for ...() function
    //  compared with num_context == 4, here is recursive elimination!
    //    due to num_context == 5, 
    //    i.e. inter-location / many-locations
    //  output_file: **new_3_many**

    //    dualize using a clump
    int nd = fd->get_dimension();
    //    obtain a polyhedron characterizing "trivial"
    trivial = new C_Polyhedron(nd, UNIVERSE);
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_to_trivial(trivial);
    }
    //    now dualize each location
    C_Polyhedron initp(nd, UNIVERSE); // for the dualized initial conditions
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->make_context();
      (*vi)->compute_dual_constraints(initp);
    }

    //    now dualize the transition systems and collect the "clumps"
    vector<Clump> vcl;
    for (vector<TransitionRelation *>::iterator vj = trlist->begin(); vj < trlist->end(); vj++){
      (*vj)->compute_consecution_constraints(vcl, initp);
    }
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_clump(vcl);
      //    this also should trigger the simplification of the context
    }
    //  Here is the function of "extract_invariant_by_eliminating()"
    dfs_traverse_timer.restart();
    dfs_traverse_for_binary_eliminating(vcl, initp);
    dfs_traverse_timer.stop();
    dfs_traverse_time = dfs_traverse_timer.compute_time_elapsed();

  } //    else if (num_context == 5)
  else if (num_context == 6){
    //  Implementation for Eliminate_c_through_inter_Location() function
    //  compared with num_context == 3, here is elimination!
    //    due to num_context == 6, 
    //    i.e. inter-location / many-locations
    //  output_file: **newdfs**

    //    dualize using a clump
    int nd = fd->get_dimension();
    //    obtain a polyhedron characterizing "trivial"
    trivial = new C_Polyhedron(nd, UNIVERSE);
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_to_trivial(trivial);
    }
    //    now dualize each location
    C_Polyhedron initp(nd, UNIVERSE); // for the dualized initial conditions
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->make_context();
      (*vi)->compute_dual_constraints(initp);
    }

    //    now dualize the transition systems and collect the "clumps"
    vector<Clump> vcl;
    for (vector<TransitionRelation *>::iterator vj = trlist->begin(); vj < trlist->end(); vj++){
      (*vj)->compute_consecution_constraints(vcl, initp);
      if (total_time.compute_time_elapsed() >= weave_time){
          cout<< "Time is up!"<<endl;
          break;
      }
    }
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_clump(vcl);
      if (total_time.compute_time_elapsed() >= weave_time){
          cout<< "Time is up!"<<endl;
          break;
      }
      //    this also should trigger the simplification of the context
    }

    dfs_traverse_timer.restart();
    for (int target_index=0; target_index<loclist->size(); target_index++){

      single_weave_count = 0;
      single_bang_count = 0;
      single_collect_time = 0;
      single_dfs_traverse_timer.restart();

      dfs_traverse_for_one_location_by_eliminating(target_index, vcl, initp);

      single_dfs_traverse_timer.stop();
      vector_single_dfs_traverse_time.push_back(single_dfs_traverse_timer.compute_time_elapsed());
      vector_single_weave_count.push_back(single_weave_count);
      vector_single_bang_count.push_back(single_bang_count);
      vector_single_collect_time.push_back(single_collect_time);
    }
    dfs_traverse_timer.stop();
    dfs_traverse_time = dfs_traverse_timer.compute_time_elapsed();

  }//    else if (num_context == 6)
  else if (num_context == 7){
    //  output_file: **newdfs_sequences**

    //  nd
    int nd = fd->get_dimension();
    //  trivial
    trivial = new C_Polyhedron(nd, UNIVERSE);
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_to_trivial(trivial);
    }
    //  initp
    C_Polyhedron initp(nd, UNIVERSE);
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->make_context();
      (*vi)->compute_dual_constraints(initp);
    }
    //  vcl
    vector<Clump> vcl;
    for (vector<TransitionRelation *>::iterator vj = trlist->begin(); vj < trlist->end(); vj++){
      (*vj)->compute_consecution_constraints(vcl, initp);
      if (total_time.compute_time_elapsed() >= weave_time){
          cout<< "Time is up!"<<endl;
          break;
      }
    }
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_clump(vcl);
      if (total_time.compute_time_elapsed() >= weave_time){
          cout<< "Time is up!"<<endl;
          break;
      }
      //    this also should trigger the simplification of the context
    }

    dfs_traverse_timer.restart();
    vector<vector<vector<vector<int>>>> target_sequences;
    for (int target_index=0; target_index<loclist->size(); target_index++){
      single_pre_prune_bang_count = 0;
      single_dfs_sequences_generation_timer.restart();

      dfs_sequences_generation_traverse(target_sequences, target_index, vcl, initp);

      single_dfs_sequences_generation_timer.stop();
      vector_single_dfs_sequences_generation_time.push_back(single_dfs_sequences_generation_timer.compute_time_elapsed());
      vector_single_pre_prune_bang_count.push_back(single_pre_prune_bang_count);
    }
    //Clear_Location_Invariant();
    for (int target_index=0; target_index<loclist->size(); target_index++){
      single_weave_count = 0;
      single_collect_time = 0;
      single_post_prune_bang_count = 0;
      single_dfs_sequences_traverse_timer.restart();

      vector<vector<vector<int>>> sequences = target_sequences[target_index];
      dfs_sequences_traverse_for_one_location_by_eliminating(sequences, target_index, vcl, initp);

      single_dfs_sequences_traverse_timer.stop();
      vector_single_dfs_sequences_traverse_time.push_back(single_dfs_sequences_traverse_timer.compute_time_elapsed());
      vector_single_weave_count.push_back(single_weave_count);
      vector_single_collect_time.push_back(single_collect_time);
      vector_single_post_prune_bang_count.push_back(single_post_prune_bang_count);
    }
    dfs_traverse_timer.stop();
    dfs_traverse_time = dfs_traverse_timer.compute_time_elapsed();

  }//    else if (num_context == 7)
  total_time.stop();
  Print_Location();
  Print_Status_after_Solver();
  if (inv_check){
    check_invariant_ok();
  }
  
  /*
  cout<<endl<<"Doing Initial Propagation"<<endl;
  Timer prop_timer;
  do_some_propagation();
  prop_timer.stop();
  cout<<"Propagation done -- Time Taken (0.01S):" <<prop_timer.compute_time_elapsed()<<endl;
  
  if (dual){
    cout<<endl<<"---- Running Cousot-Halbwachs dual propagation/narrowing----"<<endl;
    Timer dual_time;
    
    InvariantMap dualmap(f, *loclist);
    global_system->compute_dual_invariant(dualmap);
    
    dual_time.stop();
    cout<<endl<<"Time taken for Dual (0.01 S)"<<dual_time.compute_time_elapsed()<<endl;
    cout<<"--------------------------------------------------------"<<endl;
  }

  InvariantMap h79map(f, *loclist);
  if (ch79){
    cout<<endl<<"---- Running Cousot-Halbwachs with H79 widening ----"<<endl;
    Timer h79_time;
    
    global_system->compute_invariant_h79(h79map);
    
    h79_time.stop();
    cout<<"Time taken for Cousot-Halbwachs Widening (0.01 S)"<<h79_time.compute_time_elapsed()<<endl;
    cout<<"The bake-off results vs. CH79"<<endl;
    print_bake_off(h79map);
    if (inv_check){
      cout<<"Checking...."<<endl;
      h79map.check_consecution(trlist);
      cout<<"Done!"<<endl;
    }
    cout<<"--------------------------------------------------------"<<endl;
  }
   
  InvariantMap bhrz03map(f, *loclist);
  if (bhrz03){
    cout<<endl<<"---- Running Cousot-Halbwachs with BHRZ03 widening ----"<<endl;
    Timer bhrz03_time;
    
    global_system->compute_invariant(bhrz03map);
    
    bhrz03_time.stop();
    cout<<"Time taken for BHRZ03 (0.01 S)"<<bhrz03_time.compute_time_elapsed()<<endl;
    cout<<"The bake-off results vs. BHRZ03"<<endl;
    print_bake_off(bhrz03map);
    if (inv_check){
      cout<<"Checking...."<<endl;
      bhrz03map.check_consecution(trlist);
      cout<<"Done!"<<endl;
    }
    cout<<"--------------------------------------------------------"<<endl;
  }
  */
   
  return 0;
}


void collect_generators(vector<Context *> * children , Generator_System & g){
   vector<Context *>::iterator vk;
    for(vk=children->begin();vk < children->end(); vk++){
       (*vk)->collect_generators(g);
    }
}


void add_preloc_invariants_to_transitions(){
   vector<TransitionRelation *>::iterator vtr;
   for (vtr=trlist->begin(); vtr < trlist->end(); ++vtr){
      (*vtr)->add_preloc_invariant();
   }
   return;
}

void print_status(){

   cout<<"---------------------------------------------------"<<endl;
   cout<<" Local invariants to be generated : "<<zero<<endl;
   cout<<" Increasing invariants to be generated : "<<zero<<endl;
   cout<<" Strategy ID #"<<num_context<<endl;
   cout<<" # of initial propagation steps:"<<prop_steps<<endl;
   cout<<" Weave Time allowed:"<<weave_time<<endl;
   cout<<" Cousot-Halbwachs to be performed:"<<ch79<<endl;
   cout<<" BHRZ03 to be performed:"<<bhrz03<<endl;
   cout<<"----------------------------------------------------"<<endl;
}

void print_bake_off( InvariantMap const & invmap){
   bool disjoint;
   int r2;

   vector<Location *>::iterator vl;
   
   for (vl=loclist->begin(); vl <loclist->end(); vl ++){
      r2=0;
      disjoint=true;
      
      string const & what=(*vl)->get_name();
      C_Polyhedron & loc_inv= (*vl)->invariant_reference();
      C_Polyhedron const & other_inv = invmap(what);
      
      cout<<"Location :"<<what<<" ";
      
      // Am I stronger   
      if (other_inv.contains(loc_inv)){
         r2++; // I am one up
         disjoint=false;
      }
      // Is the other_inv stronger?
      
      if (loc_inv.contains(other_inv)){
            r2--; // h79 is one up
            disjoint=false;
      }

      if (disjoint) {
         cout<<"Disjoint"<<endl;
      } else if (r2 > 0){
         cout<<" + "<<endl;
      } else if (r2 <0 ){
         cout<<" - "<<endl;
      } else if (r2==0){
         cout<<" == "<<endl;
      } else {
         // this is unreachable (or is it? :-)
         cout<<" <<Unknown Relation>>"<<endl;
      }
        
   }
}

void check_invariant_ok(){
  cout<<endl<<"> > > In check_invariant_ok()";
   cerr<<"Checking for invariant..."<<endl;
   vector<TransitionRelation *>::iterator vi;
   for (vi=trlist->begin(); vi != trlist->end(); ++vi){
      (*vi)->check_map();
   }
   cerr<<"Done!"<<endl;
  cout<<endl<<"< < < Out of check_invariant_ok()";
}
