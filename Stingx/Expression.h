
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
 * Filename: Expression
 * Author: Sriram Sankaranarayanan<srirams@theory.stanford.edu>
 * Comments: Represents a parametric linear expression. Implemented as an array of
 *           LinExprs. Operations supported are factorization, transformations, simplification,
 *           and other basic construction operations like addition, subtraction, assignments etc..
 * Post-comments: LinExpr s have been swapped out by SparseLinExpr (nearly 20% space savings) and
 *               Arrays have been replaced by vectors. STL rules :-)
 *
 * Copyright: Please see README file.
 */



#ifndef __EXPRESSION__H_

#define __EXPRESSION__H_
#include <vector>
#include "var-info.h"
#include "Rational.h"
#include "SparseLinExpr.h"
#include "LinTransform.h"
#include "MatrixStore.h"

using namespace std;

class Expression{

   // n = no. of lin variables
   // r = no. of non-linear variables
   // Operations include
   //     1. Construct
   //        1.1 Add two expressions
   //        2.2 Set a linear expression for a against non-linear multiplier
   //     2. Test for two types of "purity" - type a = linear equality
   //                                       - type b = transform expression
   //     3. If pure A then convert to a linear expression
   //     4. Perform a given linear transformation over the non-linear variables, to eliminate one of them
   //     5. Factorize an expression
   //         5.1 Convert to Saclib representation
   //         5.2 factorize inside Saclib and re-interpret the results
   //     6. Simplify an against a constraint store

  private:
   int n,r; // the number of linear and multiplier variables resp.
   var_info * fn, * fr; //Mostly for printing purposes

   vector<SparseLinExpr>  l; // An r+1 dimension array of linear expressions

   SparseLinExpr  lin_fact; // The linear factor 
   LinTransform tr_fact; // the transform factor

   
   bool factored;
   int count;

   
   void initialize(int n, int r, var_info * fn, var_info * fr);

   void zero_out();
   
  public:

   Expression(int n, int r, var_info * fn, var_info * fr);
   ~Expression();
   Expression(Expression const & e);
   Expression(Expression * e1, Expression * e2);

   // add subtract, access, assign etc...
   
   Expression  operator+ ( Expression const & p1) const; // Addition
   Expression &  operator+= (Expression const & p1); // Addition to self
   Expression  operator- ( Expression const & p1) const; // Subtraction
   Expression&  operator-= (Expression const & p1); // Subtraction from self
   Expression&  operator= (Expression const & p1); // Assignment
   SparseLinExpr & operator[](int i); // Reference to the linear expression corr. to multipler i
   SparseLinExpr operator()(int i) const;// constant reference

   // accessors
   int get_n() const;
   int get_r() const;
   var_info * get_fr() const;
   var_info * get_fn() const;
   
   // Count to keep track of the freq of occurrence
   // of the factors among the other constraints
   void reset_count();
   void add_count(int i=1);
   int get_count();
   
   
   bool is_pure_a() const; // Is the expression purely linear
   bool is_pure_b() const; // Is the expression purely linear in the multipliers?
   
   
   SparseLinExpr & convert_linear() ; // CALL: Only if the expression is_pure_a else I will throw an exception
   LinTransform convert_transform() const; // call only if is_pure_b is true or else exception will be thrown

   // Call only if factorizable
   SparseLinExpr & get_linear_factor();   
   LinTransform & get_transform_factor();

   // convert the generator to a linear expression
   // Post-comments: This line of research has been disabled will revive soon.
   SparseLinExpr to_transform(Generator const & g); 
   
   

   // perform a linear transformation specified by l on the expression
   void transform(LinTransform  & l); 

   // Simplify using the store c
   void simplify(MatrixStore const & c);

   // get the lcm of all the denominators
   int get_denominator_lcm() const;
   // get the gcd of all the numerators
   int get_numerator_gcd() const;
   
   void adjust();

   // void compute_dpl_form();

   // is the expression factorizable.. side effect: split into factors
   bool factorize();
   // has the expression already been factored into two factors?
   bool is_factored() const;

   // is the expression a non-zero constant : bad name for function
   bool is_inconsistent() const;
   //is the expression a constant
   bool is_constant() const;
   // is it zero
   bool is_zero() const;
   // print factors of the expression
   
   void print_factors( ostream & os) const;
   // clone the expressoin
   Expression * clone() const;
   // count non-zero multipliers
   void count_multipliers(int * t);
   
   // If the expression is factorizable and that the
   // lintransform part matches lt then drop the transform part
   void drop_transform(LinTransform & lt); 

   // Does the expression factorize and its transform match lt?
   bool transform_matches(LinTransform & lt); 

   // is multiplier index associated with a non-zero expression
   bool is_multiplier_present(int index);
   
};

ostream & operator<<(ostream & os, Expression const & p);   

// scaling operators
Expression operator* (int i, Expression const & p1);
Expression operator* (Expression const & p1, int i);




#endif
