
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

#include <iostream>
#include <vector>
#include "Rational.h"
#include "SparseLinExpr.h"
#include "MatrixStore.h"
#include "LinTransform.h"
#include "Expression.h"
#include "ExpressionStore.h"

void ExpressionStore::initialize(int n, int r, var_info * fn, var_info * fr){
   
   this->n=n;
   this->r=r;
   this->fn=fn;
   this->fr=fr;

   le_list= new vector<SparseLinExpr>();
   lt_list= new vector<LinTransform>();
   /*
   m.init_set(n,fn);
   split_seq=new vector<LinTransform>();
   vl = new vector<Expression>();
   */
   
}

ExpressionStore::ExpressionStore(int n, int r, var_info * fn, var_info * fr){
   initialize(n,r,fn,fr);
   
}

bool ExpressionStore::add_expression(Expression&  exp){
   Expression * e = new Expression(exp);

   /* if (exp.is_pure_a()){
      add_linear_expression(e->convert_linear());
      return true;
      } */
   
   vl->push_back(*e);
   return false;
}

/*
void ExpressionStore::add_linear_expression(SparseLinExpr  exp){
   m.add_constraint(exp);
   
}
*/


void ExpressionStore::add_transform(LinTransform  lt){
   
   vector<Expression >::iterator vi;

   for (vi=vl->begin();vi < vl->end();vi ++){
      (*vi).transform(lt);
   }

   
}

void ExpressionStore::remove_trivial(){
   // look for zero expressions and remove them vector<Expression >::iterator vi;
   vector<Expression >::iterator vi;
   vi=vl->begin();
   while(vi < vl->end() && (*vi).is_zero()){
      vl->erase(vi);
      vi=vl->begin();
   }
   
   for (;vi < vl->end();vi ++){
      if ((*vi).is_zero()) {
         vl->erase(vi);
         vi--;
      }
   }
   
   return;
   
}


/*
bool ExpressionStore::is_consistent(){
   
   if (!m.is_consistent()){
      return false;
   } 

   vector<Expression >::iterator vi;

   for (vi=vl->begin();vi < vl->end();vi ++){
      if ((*vi).is_inconsistent()) {
         return false;
      }
   }

   return true;


}

*/


void ExpressionStore::simplify( MatrixStore const & m ){
   //   bool f=true;
   vector<Expression>::iterator vi;
   SparseLinExpr ll;
   LinTransform lt(n,fn);
   
   //   while (f){
      
   remove_trivial();

     
      // Now take each expression and simplify it

   for (vi=vl->begin();vi <vl->end();vi++)
      (*vi).simplify(m);

   
      /* This can only be done for equality stores 
         for (vi=vl->begin();vi <vl->end();vi++){
         if ((*vi).is_pure_a()){
         f=true;
            
         ll=(*vi).convert_linear();
         cout<<"Adding Lin Exp"<< ll<<endl;
         add_linear_expression(ll);
         } else if ((*vi).is_pure_b()){
         f=true;
         lt=(*vi).convert_transform();
         add_transform(lt);
         cout<<"Adding Linear Transform "<<lt<<endl;
         }
         
      }
      
      */
   remove_trivial();
   
   //}

   
   return;
}

/*
MatrixStore & ExpressionStore::get_m(){
   return m;
}

*/
vector<Expression> * ExpressionStore::get_vl(){
   return vl;
}

ostream & operator<< (ostream & os, ExpressionStore & es){
   
   vector<Expression>::iterator vi;
   vector<Expression> * vl= es.get_vl();
   os<<"The Expressions are:"<<endl;
   for (vi=vl->begin();vi< vl->end();vi++){
      os<<(*vi)<<endl;
   }

   return os;
}


vector<SparseLinExpr>::iterator ExpressionStore::lin_expr_collected(SparseLinExpr const & l) const {
   vector<SparseLinExpr>::iterator vi;
   for(vi=le_list->begin(); vi < le_list->end() ; vi ++){
      if ((*vi)==l)
         return vi;
   }

   return vi;
}


vector<LinTransform>::iterator ExpressionStore::lin_transform_collected(LinTransform const & l) const {
   vector<LinTransform>::iterator vi;
   for(vi=lt_list->begin(); vi < lt_list->end() ; vi ++){
      if ((*vi)==l)
         return vi;
   }

   return vi;
}



bool ExpressionStore::collect_factors(){
   vector<Expression>::iterator vi;
   vector<SparseLinExpr>::iterator vj;
   vector<LinTransform>::iterator vk;
   bool some=false;
   for(vi=vl->begin();vi < vl->end(); vi++){
      if ((*vi).factorize()){
         some=true;
         vj= lin_expr_collected((*vi).get_linear_factor());
         if (vj < le_list->end())
            (*vj).count_up();
         else
            le_list->push_back((*vi).get_linear_factor());
         
         vk= lin_transform_collected((*vi).get_transform_factor());
         
         if (vk < lt_list->end())
            (*vk).count_up();
         else
            lt_list->push_back((*vi).get_transform_factor());
         
      }


      
   }

   cout<<"Collecting Factors:"<<endl;
   
   for(vj=le_list->begin();vj < le_list->end();vj++)
      cout<<(*vj)<< "  Occurs "<< (*vj).get_count()<<endl;

   for(vk=lt_list->begin();vk < lt_list->end();vk++)
      cout<<(*vk)<< "  Occurs  "<< (*vk).get_count()<<endl;

   
   return some;
   
}

/*
void ExpressionStore::set_store(MatrixStore &mat){
   for (int i=0;i<n;i++)
      for (int j=0;j<n+1;j++)
         m(i,j)=mat(i,j);
   
   return;
}



void ExpressionStore::split_on_transform( LinTransform const & lt){
   // Split on a linear transform
   // create two children expression stores and then
   // browse through all the expressions
   // If the expression does not factorize
   //            then add it to both the stores
   // else if the transformation factor is incompatible
   //            then add it to both the stores
   // else
   //            add the transform factor to store1 and the linear factor to store 2
   // simplify the resulting expressions and push them into the children

   ExpressionStore * child1, * child2;

   child1=new ExpressionStore(n,r,fn,fr);
   child2=new ExpressionStore(n,r,fn,fr); // Initialize the children

   vector<Expression>::iterator vi;
   bool some=false;
   
   child1->set_store(m);
   child2->set_store(m);
   
   for (vi=vl->begin();vi < vl->end();vi++){
      if ((*vi).factorize() && (*vi).get_transform_factor()==lt) {
         cout<<"Split: adding "<<(*vi).get_linear_factor()<<endl;
         child2->add_linear_expression((*vi).get_linear_factor());
         some=true;
      } else {
         child1->add_expression(*vi);
         child2->add_expression(*vi);
      }  
   }

   child1->set_split_seq(split_seq);

   child2->set_split_seq(split_seq);
   child2->add_to_split(lt);
   
   if (some)
      child1->add_transform(lt);
   
   children->push_back(child1);
   children->push_back(child2);
   cout<<"Split # 1"<<endl;
   cout<<(*child1)<<endl;

   cout<<"Split # 2"<<endl;
   cout<<(*child2)<<endl;

   
}

void ExpressionStore::split_on_transform_already_split( LinTransform const & lt){
   // Split on a linear transform
   // create two children expression stores and then
   // browse through all the expressions
   // If the expression does not factorize
   //            then add it to both the stores
   // else if the transformation factor is incompatible
   //            then add it to both the stores
   // else
   //            add the transform factor to store1 and the linear factor to store 2
   // simplify the resulting expressions and push them into the children

   ExpressionStore * child1;

   child1=new ExpressionStore(n,r,fn,fr);
   

   vector<Expression>::iterator vi;
   bool some=false;
   
   child1->set_store(m);
   
   
   for (vi=vl->begin();vi < vl->end();vi++){
      if ((*vi).factorize() && (*vi).get_transform_factor()==lt) {
         child1->add_linear_expression((*vi).get_linear_factor());
         some=true;
      } else {
         child1->add_expression(*vi);
      }  
   }

   child1->set_split_seq(split_seq);

   
   
   children->push_back(child1);
   
   cout<<"Split # 1"<<endl;
   cout<<(*child1)<<endl;

   
   
}


void ExpressionStore::strategize(){

   children=new vector<ExpressionStore*>();

   simplify();

   if (!collect_factors()){
      cerr<<"Leaf Node:"<<endl<<"---------------------------------"<<endl;
      cerr<<*this<<endl;
      cerr<<"-----------------------------------"<<endl;
      return;
   }
   // find the most frequent linear transform.

   cout<<"-----------------------------------------------"<<endl;
   cout<<"Splitting:  "<<*this<<endl;
   cout<<"-----------------------------------------------"<<endl;
   
   int max=0;
   vector<LinTransform>::iterator vi,vj;
   vector<ExpressionStore *>::iterator vc;

   vj=lt_list->begin();
   
   for(vi=lt_list->begin();vi < lt_list->end(); vi++){
      if ((*vi).get_count() >= max){
         max= (*vi).get_count();
         vj=vi;
      }
   }
   
   cout<<"Detected Maximum  "<< (*vj)<<endl;
   if (!already_split(*vj)) {    
      split_on_transform(*vj);
   } else {
      split_on_transform_already_split(*vj);
   }
   
   for (vc=children->begin();vc < children->end(); vc++)
      (*vc)->strategize();


}

void ExpressionStore::set_split_seq(vector<LinTransform>* split){
   vector<LinTransform>::iterator vi;
   for (vi=split->begin();vi < split->end();vi++)
      split_seq->push_back(*vi);
}

void ExpressionStore::add_to_split(LinTransform const & lt){
   split_seq->push_back(lt);
}

bool ExpressionStore::already_split (LinTransform const & lt){
   vector<LinTransform>::iterator vi;
   for (vi=split_seq->begin();vi < split_seq->end();vi++)
      if ((*vi)==lt)
         return true;

   return false;
   
}


*/
