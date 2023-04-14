
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

#include "myassertions.h"
#include "PolyUtils.h"
#include "DualTransitionRelation.h"

using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;


bool DualTransitionRelation::add_guard(Constraint const & cc){
   Linear_Expression ll(0);
   int i,j;
   
   bool flag=true;
   
   for(i=0;i<n_+1;++i){
      flag = handle_integers(cc.coefficient(Variable(i+n_+1)),j);
      if (!flag || j!=0)
         return false;
      ll+= cc.coefficient(Variable(i)) * Variable(i);
   }
   ll+=cc.inhomogeneous_term();

   if (cc.is_equality())
      guard_.add_constraint(ll==0);
   else if (cc.is_nonstrict_inequality())
      guard_.add_constraint(ll>=0);
   else if (cc.is_strict_inequality())
      guard_.add_constraint(ll > 0);
   else {
      INVARIANT ( false, "DualTransitionRelation::add_guard() -- should not reach here in the first place ");  
   }
   return true;
}

void DualTransitionRelation::split_relation(){
   // split unsat_ into guard_ and update_

   // guard_ and update_ should be initialized to n_+1 and 2n_+1
   // dimensional polyhedra respectively

   PRECONDITION( guard_.space_dimension()==(unsigned) (n_+1) &&
                 update_.space_dimension()== (unsigned) 2*(n_+1),
                 " DualTransitionRelation::split_relation()... precondition violated ");

   Constraint_System cs=sat_.minimized_constraints();
   Constraint_System::const_iterator vi;

   for (vi=cs.begin(); vi!=cs.end(); ++vi){
      if (!add_guard(*vi))
         update_.add_constraint((*vi));
   }

   // DEBUG INFO
   
   return;
}


void DualTransitionRelation::manufacture_dual_var_info(){
   int i;
   fd_=new var_info();
   for (i=0;i<n_;++i){
      string x(f_->get_name(i));
      x= "c_"+x+"_0";
      fd_->insert(x.c_str());
   }
   
   fd_->insert("d_0");
   
   for (i=0;i<n_;++i){
      string x(f_->get_name(i));
      x= "c_"+x+"_1";
      fd_->insert(x.c_str());
   }
   
   fd_->insert("d_1");

   
}

DualTransitionRelation::DualTransitionRelation(var_info * f,  C_Polyhedron const & unsat,
                                               C_Polyhedron const & sat, Location * preloc, Location * postloc):
      n_(f->get_dimension()),
      f_(f),
      sat_(sat),
      unsat_(unsat),
      guard_(n_+1,UNIVERSE),
      update_(2*n_+2,UNIVERSE),
      preloc_(preloc),
      postloc_(postloc),
      fired_(false)
{
   // manufacture a dual var info
   manufacture_dual_var_info();
   // perform a class invariant check
   //   INVARIANT( OK__ (), " DualTransitionRelation::DualTransitionRelation(...) invariant failed ");
   split_relation();
}




bool DualTransitionRelation::OK__ (){


   return (sat_.space_dimension() == (unsigned ) (2* (n_+1)) )  && (unsat_.space_dimension() == (unsigned ) ((n_+1)) );

   
}


void DualTransitionRelation::print( ostream & out ) const {
   // print the contents
   
   out << "Dual Transition Relation : "<<preloc_->get_name()<<" --->"<< postloc_->get_name()<<endl;
   out<< " Sat [["<<endl;
   print_polyhedron(out,sat_,fd_);
   out <<"]] "<<endl;
   out<< " UnSat [["<<endl;
   print_polyhedron(out,unsat_,fd_);
   out <<"]] "<<endl;
   
}



void DualTransitionRelation::compute_post_new(C_Polyhedron const & what, C_Polyhedron & result)  {
   
   PRECONDITION (what.space_dimension() == (unsigned) (n_+1),
                 "DualTransitionRelation::compute_post - input's space dimension mismatch expected "
                 <<(n_+1) <<" obtained "<<what.space_dimension());
   
   result=C_Polyhedron(what);
   
   // check that result /\ unsat = false
   
   if (!fired_){
      result.intersection_assign(unsat_);
      
      if (!result.is_empty()) {
         result=C_Polyhedron(n_+1, UNIVERSE);
         return;
      }
      fired_=true;
      
      result=C_Polyhedron(what);
   }
   
   // insert n_+1 dimensions into the result
   result.intersection_assign(guard_);
   
   result.add_space_dimensions_and_embed(n_+1);
   
   // now intersect with sat
   // but use generalized_affine image
   
   // result.intersection_assign(sat_);
   
   Constraint_System cs = update_.minimized_constraints();
   Constraint_System::const_iterator vi;

   Linear_Expression left,right;


   for (vi = cs.begin(); vi != cs.end(); ++vi ){
      // Convert the constraint into an affine transform
      // and apply
      
      set_up_affine_transform(n_+1,(*vi), left,right);
      
      
      if ((*vi).is_equality())
         result.generalized_affine_image(left,EQUAL,right);
      else {
         result.add_constraint((*vi));
      }
         
      // done
   }
   
   
   Variables_Set vs;
   for (int i=0; i<=n_;++i)
      vs.insert(Variable(i));

   result.remove_space_dimensions(vs);

   return; // done
   
}

void DualTransitionRelation::compute_post( C_Polyhedron const & what, C_Polyhedron & result) const{

   PRECONDITION (what.space_dimension() == (unsigned) (n_+1),
                 "DualTransitionRelation::compute_post - input's space dimension mismatch expected "
                 <<(n_+1) <<" obtained "<<what.space_dimension());
   
   result=C_Polyhedron(what);

   // check that result /\ unsat = false

   result.intersection_assign(unsat_);

   if (!result.is_empty()) {
      result=C_Polyhedron(n_+1, UNIVERSE);
      return;
   }
   
   result=C_Polyhedron(what);
   // insert n_+1 dimensions into the result
   
   result.add_space_dimensions_and_embed(n_+1);
   
   // now intersect with sat
   //PPL-0.9
   //result.intersection_assign_and_minimize(sat_);
   //PPL-1.2
   result.intersection_assign(sat_);

   Variables_Set vs;
   for (int i=0; i<=n_;++i)
      vs.insert(Variable(i));

   result.remove_space_dimensions(vs);

   return; // done
}


ostream & operator<< (ostream & out, DualTransitionRelation const & dtr){
   dtr.print(out);
   return out;
}

