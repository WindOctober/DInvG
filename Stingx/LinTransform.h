
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
 * Filename: LinTransform
 * Author: Sriram Sankaranarayanan<srirams@theory.stanford.edu>
 * Comments: Same as LinExpr. The coefficients are understood to be multiplier variables here.
 * Post-Comments: A more efficient implementation called SparseLinTransform is available for sparse cases.
 * Copyright: Please see README file.
 */

#ifndef __LIN__TRANSFORM__H_

#define __LIN__TRANSFORM__H_

#include <iostream>
#include "Rational.h"
#include "LinExpr.h"

using namespace std;

class LinTransform: public LinExpr{
  public:
   LinTransform();
   LinTransform(int n, var_info * fn);
   int get_base() const;
   bool is_trivial() const;
   bool is_inconsistent() const;
   
};

#endif
