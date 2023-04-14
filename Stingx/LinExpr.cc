
/*
 * lsting: Invariant Generation using Constraint Solving. 
 * Copyright (C) 2005 Sriram Sankaranarayanan < srirams@theory.stanford.edu>
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful, 
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 *
 */

//#include <saclib.h>
#include "myassertions.h"
#include "funcs.h"
#include "var-info.h"
#include "Rational.h"
#include <iostream>
#include "LinExpr.h"
#include "PolyUtils.h"
#include "Macro.h"
using namespace std;


void LinExpr::initialize(int n, var_info * f){
   //initialize
   this->n=n;
   this->f=f;
   lin.resize(n+1,Rational(0,0));
   count=1;
   return;
}

void LinExpr::clear_out(){
   for (int i=0;i< n+1;++i)
      lin[i]=0;
   
}

LinExpr::LinExpr(LinExpr const & ll){
   initialize(ll.get_dim(),ll.get_info());   
   for (int i=0;i<n+1;i++)
      lin[i]=ll(i);
   return;
}

bool LinExpr::is_zero() const {
   for (int i=0;i<n+1;i++){
      if (lin[i]!=0)
         return false;
   }
   return true;
}

bool LinExpr::is_constant() const{
   for (int i=0;i<n;i++){
      if (lin[i]!=0)
         return false;
   }
   return true;
}

LinExpr::~LinExpr(){
   // nothing to do here.. thanks to the array -> vector conversion
   // STL rules!
}

LinExpr::LinExpr(){
   // default constructor overloaded.
   n=0;
}

LinExpr::LinExpr(int n, var_info * f){
   initialize(n,f);
}

void LinExpr::init_set(int n, var_info * f){
   initialize(n,f);
}

inline Rational& LinExpr::operator[](int i){
   return lin[i];
}



Rational LinExpr::operator() (int i) const{
   return lin[i];
   
}

LinExpr LinExpr::operator+ ( LinExpr const & p1) const{
   LinExpr tmp(n,f);
   for(int i=0;i<n+1;i++)
      tmp[i]=lin[i]+p1(i);
   return tmp; // A reference to tmp.lin will be copied.. so this is not all that costly
   
}

LinExpr&  LinExpr::operator+= (LinExpr const & p1){
   for(int i=0;i<n+1;i++)
      lin[i]+=p1(i);

   return *(this);
}

LinExpr LinExpr::operator- ( LinExpr const & p1) const{
   LinExpr tmp(n,f);
   for(int i=0;i<n+1;i++)
      tmp[i]=lin[i]-p1(i);
   return tmp; // A reference to tmp.lin will be copied.. so this is not all that costly
   
}

LinExpr&  LinExpr::operator-= (LinExpr const& p1){
   for(int i=0;i<n+1;i++)
      lin[i]-=p1(i);

   return *(this);
}

bool LinExpr::operator== (LinExpr const & p1) const{

   // note this is an equivalence check.
   Rational factor;
   bool ret= equiv(p1,factor);
   return ret && (factor != 0);
}


LinExpr & LinExpr::operator= (LinExpr const & p1){
   // erase lin
   lin.erase(lin.begin(), lin.end());
   // reset
   initialize(p1.get_dim(),p1.get_info()); // reinitialize
   //assign
   for(int i=0;i<n+1;i++)
      lin[i]=p1(i);
   //return
    return *this;
}


LinExpr operator* (int j, LinExpr const & p1){
   int n= p1.get_dim();
   var_info* f= p1.get_info();
   LinExpr tmp(n,f);
   for(int i=0;i<n+1;i++)
      tmp[i]=p1(i) * j;
   return tmp; // A reference to tmp.lin will be copied.. so this is not all that costly
}


LinExpr operator* (LinExpr const & p1, Rational const &  i){
   int n= p1.get_dim();
   var_info* f= p1.get_info();
   LinExpr tmp(n,f);
   for(int j=0;j<n+1;j++)
      tmp[j]=i * p1(j);
   return tmp; // A reference to tmp.lin will be copied.. so this is not all that costly
}

LinExpr operator* ( Rational const &  i,LinExpr const & p1){
   int n= p1.get_dim();
   var_info* f= p1.get_info();
   LinExpr tmp(n,f);
   for(int j=0;j<n+1;j++)
      tmp[j]=i*p1(j);
   return tmp; 
}


LinExpr&  LinExpr::operator*= (Rational const & j){
   for(int i=0;i<n+1;i++)
      lin[i]*= j;
   return *this; 
}


LinExpr&  LinExpr::operator*= (int j){
   Rational r1(j,1);
   for(int i=0;i<n+1;i++)
      lin[i]*= r1;
   return *this; 
}



void LinExpr::print(ostream & os) const{

   //
   // print the contents into os
   //
   
   int j;
   bool sp=false;
   
   if (is_constant() && lin[n] ==0){
      os<<"0";
      return;
   }
   
   
   for(j=0;j<n;++j){
      if (lin[j]==0)
         continue;
      if (!sp ){
         sp=true;
         os<<lin[j] <<" * " <<f->get_name(j) <<" ";
      } else {
         if (!(lin[j] < 0))
            os <<" + ";
         
         os<< lin[j] <<" * "<<f->get_name(j)<<" ";
      }
   }
   if (lin[n]==0)
      return;
   
   if (!(lin[n] < 0))
      os <<" + ";
   
   os <<lin[n];

   return;
}

void LinExpr::print_in_arrinv() const{
   int j;
   bool sp=false;
   f->to_array_invariant();
   
   if (is_constant() && lin[n] ==0){
      tcout<<"0";
      return;
   }
   
   for(j=0;j<n;++j){
      if (lin[j]==0)
         continue;
      if (!sp){
         sp=true;
         tcout<<lin[j]<<" * "<<f->get_arr_name(j) <<" ";
      } else {
         if (!(lin[j] < 0))
            tcout<<"+";
         
         tcout<<lin[j]<<" * "<<f->get_arr_name(j)<<" ";
      }
   }
   if (lin[n]==0)
      return;
   
   if (!(lin[n] < 0))
      tcout<<" + ";
   
   tcout<<lin[n];

   return;
}

ostream & operator<< (ostream & os, LinExpr const & expr){
   expr.print(os);
   return os;
}





int LinExpr::get_dim() const{
   return n;
}
var_info * LinExpr::get_info() const{
   return f;
}



int LinExpr::get_denominator_lcm() const{
    int run=1,j;
    for (int i=0;i<n+1;i++){
       if ((j=lin[i].den())!=0) // Zero denominators are catastrophical..
         run=lcm(run,j);
   }
   return run;
}

int LinExpr::get_numerator_gcd()const{
   bool first_number_seen=false;

   int run=1,j;
   for (int i=0;i<n+1;i++){
      if ((j=lin[i].num())!=0) {
         if (first_number_seen)
            run=gcd(run,j);
         else{
            first_number_seen=true;
            run=j;
         }
      }
   }
   return run;
}


bool LinExpr::equiv(LinExpr const & l2, Rational & factor) const{
   // Check if there is a multiplying factor such that  c * this =  l_2
   // Assert l2!=0

   
   int i=0;
   
   
   while(i<n+1 && lin[i]==0) {
      if (l2(i)!=0) return false;
      i++;
   }

   factor=l2(i) * lin[i].inv();

   while( i<n+1){
      if (factor*lin[i]!= l2(i))
         return false;
      i++;
   }
   return true;
   
}



int LinExpr::reset_count(){
   int t=count;
   count=0;
   return t;
}

int LinExpr::count_up(){
   return count++;
}

int LinExpr::count_down(){
   return count--;
}



Linear_Expression LinExpr::to_lin_expression() const{

   int j=get_denominator_lcm();
   int num,den;
   num=lin[n].num();
   den=lin[n].den();
   Linear_Expression l( num*j/den ); // set the constant term
   for (int i=0;i<n;i++){
      num=lin[i].num();
      den=lin[i].den();
      l= l+ (num*j/den) * Variable(i);
   }
   return l;
      
}


Constraint LinExpr::get_constraint(int ineq_type) const{
   Linear_Expression l = to_lin_expression();
   switch(ineq_type){
      case TYPE_LEQ:
         return l <= 0;
      case TYPE_EQ:
         return l==0;
      case TYPE_GEQ:
         return l >= 0;
      case TYPE_GE:
         return l > 0;
      case TYPE_LE:
         return l < 0;
         
   }
   return l==0; // by default
}

// ***
// Old version, StInG compling under PPL 1.2 (05/11/2021),
// updates by Hongming Liu, in Shanghai Jiao Tong University.
// ***
/*
Rational LinExpr::evaluate(Generator const & g){
   Rational ret;// always initializes to 0
   Linear_Expression l1(g);
   int m;
   for(int i=0;i<n;i++){
      m=handle_integers(l1.coefficient(Variable(i)));
      ret=ret+ m* lin[i];
   }
   ret=ret+lin[n];

   return ret;
}
*/

// ***
// New version, StInG compling under PPL 1.2 (05/11/2021),
// updates by Hongming Liu, in Shanghai Jiao Tong University.
// ***
Rational LinExpr::evaluate(Generator const & g){
   Rational ret;// always initializes to 0
   Linear_Expression l1;
   for (dimension_type i = g.space_dimension(); i-- >0; ){
      l1 += g.coefficient(Variable(i)) * Variable(i);
   }
   
   int m;
   for(int i=0;i<n;i++){
      m=handle_integers(l1.coefficient(Variable(i)));
      ret=ret+ m* lin[i];
   }
   ret=ret+lin[n];

   return ret;
   
}
