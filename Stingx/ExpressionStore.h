
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
 * Filename: ExpressionStore
 * Author: Sriram Sankaranarayanan<srirams@theory.stanford.edu>
 * Comments: Container for expressions with some utilites for choosing factors and
 *           cloning. Primarily used as the parametric linear constraint store by 
 *           module Context. SACRED CODE. Do not TOUCH.
 * Copyright: Please see README file.
 */


#ifndef __EXPRESSION__STORE__H_
#define __EXPRESSION__STORE__H_


#include <iostream>
#include <vector>
#include "Rational.h"
#include "SparseLinExpr.h"
#include "MatrixStore.h"
#include "LinTransform.h"
#include "Expression.h"

using namespace std;

class ExpressionStore{
  private:


   
   // A set of expressions.
   // Basic Operations include
   //                  1. Creation of a store
   //                  2. Sorting Expressions
   //                  3. Simplifying Expressions using a given Matrixstore
   //                  4. Collecting linear expressions and transforms
   //                  5. factorizing and collecting the factors
   //                  6. Cloning the expression

   /*  vl = set of expressions
    *  n= no of dimensions
    *  r = no. of multipliers
    *  fn, fr = printing information for n, r variables.
    */
   
   vector<Expression > * vl;
   int n, r;
   var_info * fn, *fr ;
   
   vector<LinTransform> * lt_list;
   vector<SparseLinExpr> * le_list;
   

   void initialize(int n, int r, var_info * fn, var_info * fr);
   vector<SparseLinExpr>::iterator lin_expr_collected(SparseLinExpr const & l) const;
   vector<LinTransform>::iterator lin_transform_collected(LinTransform const & l) const;

   //vector<ExpressionStore *> * children;

   //vector<LinTransform> * split_seq;
   
  public:

   ExpressionStore(int n, int r, var_info * fn, var_info * fr);

   bool add_expression(Expression &  exp);

   //void add_linear_expression(LinExpr  exp);
   
   void add_transform(LinTransform  lt);

   void remove_trivial();

   //bool is_consistent();

   // bool dead_end();

   //void set_store(MatrixStore & s);
   
   void simplify(MatrixStore const & s);

   void set_split_seq(vector<LinTransform>* split);

   bool already_split (LinTransform const & lt);

   void add_to_split(LinTransform const & lt);
   
   bool collect_factors();
   

   //MatrixStore & get_m();

   vector<Expression> * get_vl();

   void split_on_transform(LinTransform const & lt);
   void split_on_transform_already_split(LinTransform const & lt);
   
   void strategize();
   
};

ostream & operator<< (ostream & os, ExpressionStore & es);



#endif
