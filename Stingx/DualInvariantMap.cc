
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
#include "InvariantMap.h"
#include "DualInvariantMap.h"

void DualInvariantMap::populate(){

   // dualize and add values
   
   vector<Location *>::const_iterator vi;
   for (vi=vloc_.begin(); vi != vloc_.end(); ++vi){
      C_Polyhedron dualp(n_,UNIVERSE);
      if ((*vi)->initial_poly_set()){
         C_Polyhedron const & pp = (*vi)->get_poly_reference();
         dualize(pp,dualp);
      }
      add_value_to_map((*vi)->get_name(), dualp);
         
   }
   return;
}

DualInvariantMap::DualInvariantMap(int n, var_info* fd, vector<Location *> const & vloc):InvariantMap(vloc){
   n_=n;
   f_=fd;
   populate();
}
        
void DualInvariantMap::H79_narrowing_assign (DualInvariantMap  const & im){
   vector<Location *>::const_iterator vi;

   for(vi=vloc_.begin(); vi !=vloc_.end(); ++vi){
      // obtain a name and a polyhedron
      string const & name=(*vi)->get_name();
      C_Polyhedron const  & poly = im(name);
      C_Polyhedron & my_poly = operator[](name);

      H79_narrow(my_poly,poly);
   }

   return;
}



void DualInvariantMap::primalize(InvariantMap & result){
   vector<Location *>::const_iterator vi;

   for(vi=vloc_.begin(); vi !=vloc_.end(); ++vi){
      // obtain a name and a polyhedron
      string const & name=(*vi)->get_name();
      C_Polyhedron const & my_poly = operator()(name);
      primal(my_poly,result[name]);
   }
   
   return;
}


