
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

/* 
 * Filename: DualTransitionRelation
 * Author: Sriram Sankaranarayanan<srirams@theory.stanford.edu>
 * Comments: Inactive module.. reimplemented as part of the DUCHESS effort.
 *           Code works but very bare-bones and included only because I am
 *           to lazy to remove it and fix the rest of the implementation.
 * Copyright: Please see README file.
 */


#ifndef LS__DUAL_TRANSITION_RELATION__H_

#define LS__DUAL_TRANSITION_RELATION__H_

#include "Rational.h"
#include "var-info.h"
#include "ppl.hh"
#include <vector>
#include <set>
#include <map>
#include <string>

#include "Location.h"
#include "TransitionRelation.h"

using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;

class DualTransitionRelation{
  private:


   // A dual transition relation is very similar to a primal system in
   // structure.  It has an assertion for unsat, an update assertion
   // for satisfiability.

   /*
    *  The members are 
    *   n_: The number of dimensions
    *   f_,fd_ : The primary and secondary var infos
    *   unsat_, sat_ : The two dual assertions
    *   preloc_, postloc_ : The pre and the post locations    
    */
   
   
   int n_; // the # of dimensions
   var_info * f_; // the primal  var-info
   var_info * fd_; // the dual var-info
   C_Polyhedron sat_, unsat_, guard_, update_; // unsat_ is a n_+1 dimensional polyhedron
   // sat_ is a 2n_+2 dimensional polyhedron
   Location * preloc_ , * postloc_;
   
   bool fired_;

   // For later split sat_ into equalities, and  inequalities
   // so that the process of computing post can be optimized

   bool OK__ ();

   void split_relation();
   bool add_guard( Constraint const & cc);
   
   void manufacture_dual_var_info();
   
  public:

   DualTransitionRelation(var_info * f, C_Polyhedron const & unsat, C_Polyhedron const & sat,
                          Location * preloc, Location * postloc);

   

   // compute the post condition -- take 1

   
   void compute_post(C_Polyhedron const & what,
                     C_Polyhedron & result) const;

   void compute_post_new (C_Polyhedron const & what,
                          C_Polyhedron & result);


   // pretty print the transition relation
   void print (ostream & os)const ;

   // inlines
   void clear_fired() {
      fired_=false;
   }
   
   var_info * get_var_info() const {
      return f_;
   }

   var_info * get_dual_var_info () const {
      return fd_;
   }

   C_Polyhedron const & get_sat_polyhedron_const_ref(){
      return sat_;
   }

   C_Polyhedron  & get_sat_polyhedron_ref(){
      return sat_;
   }

   
   C_Polyhedron const & get_unsat_polyhedron_const_ref(){
      return unsat_;
   }

   C_Polyhedron  & get_unsat_polyhedron_ref(){
      return unsat_;
   }
   
   string const & get_preloc_name() const{
      return preloc_->get_name();
   }

   
   string const & get_postloc_name() const{
      return postloc_->get_name();
   }
   
};



ostream&  operator<< (ostream & out, DualTransitionRelation const & dtr);

#endif
