
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
#include "SparseLinTransform.h"

using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;


void SparseLinTransform::normal_form_assign( SparseLinExpr & s) const {
   // first traverse s from back and look at the first non-zero coefficient

   PRECONDITION((s.get_dim()== _n) ,                 \
                "Error: Incompatible number of variables"  );

   
   TRMap::const_iterator vi;
   Rational factor,r;
   
   int i,k;
   
   for (vi=_m.begin(); vi!=_m.end(); ++vi){

      i=(*vi).first; // obtain the index.

      
      if (s(i)==0) continue; // nothing to be done in that case

      // if s(i) is not zero

      // first take the Corresponding transformation
      SparseLinExpr const & st= (*vi).second;

      // Transformation needs to be multiplied by factor= -s(i)
      
      factor = -1 * s(i);
      
      s.set_coefficient(i,Rational(0,0)); // replace s(i) by zero
      
      // now perform  with s(i) -= factor * st;
      
      IRMap const & irm = st.get_map(); // the map
      IRMap::const_iterator vj; // an iterator for the map

      for (vj=irm.begin(); vj !=irm.end(); ++vj){
         k=(*vj).first; // the coefficient for variable k 
         r=(*vj).second; // is r

         INVARIANT ( (r!=0),
                     "SparseLinExpr's invariant violated in SparseLinTransform");
         
         
         INVARIANT ( (k < i)         ,\
                     "SparseLinTransform --> larger variable "<<k<<" found in transform " << i );

         // add r * factor to the i-offset variable of s

         s.add_coefficient(k, r * factor);
         
      } 
      // subtraction done
      
   }

   return;
      
}


SparseLinExpr SparseLinTransform::normal_form(SparseLinExpr const & s) const {
   SparseLinExpr s1(s);
   normal_form_assign(s1);

   return s1;
}

void SparseLinTransform::add_expression( SparseLinExpr const & s){

   if (s.is_zero()) return; // I cannot add zero expressions 
   
   SparseLinExpr s1(s);
   normal_form_assign(s1); // convert s1 into a normal form
   
   // now obtain the largest non-zero coefficient in s1

   if (s1.is_zero()) return; // if s1 is implied then return

   int i=s1.obtain_largest_coefficient();
   // is i already a dependent variable?
   
   INVARIANT ( (!is_variable_dependent(i)) , " add_expression -> Error in reduction");

   _m.insert(TRPair(i,s1));

   // that should do it
}

