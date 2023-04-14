
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
#include "Rational.h"
#include "LinExpr.h"
#include "LinTransform.h"

LinTransform::LinTransform(int n, var_info * fn){
   initialize(n,fn);
}

LinTransform::LinTransform(){
   n=0;
}

int LinTransform::get_base() const{
   int i;
   for (i=0;i<n+1;i++)
      if (lin[i]!=0)
         return i;

   return i;
}

bool LinTransform::is_trivial() const{
   int i;
   for (i=0;i<n+1;i++)
      if (lin[i]!=0)
         return false;

   return true;
}


bool LinTransform::is_inconsistent() const{
    int i;
   for (i=0;i<n;i++)
      if (lin[i]!=0)
         return false;

   if (lin[n]==0) return false;

   return true;
}


