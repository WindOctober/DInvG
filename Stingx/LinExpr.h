
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
 * Filename: LinExpr
 * Author: Sriram Sankaranarayanan<srirams@theory.stanford.edu>
 * Comments: A linear expression over n variables with Rational coefficients.
 * Post-Comments: A more efficient implementation called SparseLinExpr is
 * available for sparse cases. Copyright: Please see README file.
 */

#ifndef D__LIN__EXPR__H_
#define D__LIN__EXPR__H_

#include <iostream>

#include "Rational.h"
#include "global_types.h"
#include "ppl.hh"
#include "var-info.h"

using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;

class LinExpr {
   protected:
    /*
     * members:
     *   n = dimension
     *  lin = array (later vector) of coefficient.
     *         n+1 coefficients. lin[n] is the constant term.
     *  f = printing info.
     * count = An auxilliary flag for counting occurrences, used by Context.cc
     */

    int n;
    vector<Rational> lin;
    var_info* f;
    int count;

    void initialize(int n, var_info* f);
    // set to zero.. preserving the dimensionality.
    void clear_out();

   public:
    LinExpr();
    LinExpr(int n, var_info* f);
    LinExpr(LinExpr const& ll);

    // A public way of calling initialize. I suck
    void init_set(int n, var_info* f);

    // LinExpr(int n); // Can be added later if required

    LinExpr operator+(LinExpr const& p1) const;  // Addition
    LinExpr& operator+=(LinExpr const& p1);      // Addition to self
    LinExpr operator-(LinExpr const& p1) const;  // Subtract
    LinExpr& operator-=(LinExpr const& p1);      // from self
    LinExpr& operator=(LinExpr const& p1);       // Assignment
    LinExpr& operator*=(int i);                  // scale using integer
    LinExpr& operator*=(Rational const& i);

    //
    // checks if there is a factor c such that
    //              this = c * t
    // WARNING: non-standard semantics here.

    bool operator==(LinExpr const& t) const;

    // mess around with count
    int get_count() const { return count; }
    int reset_count();
    int count_up();
    int count_down();

    // check if two linexprs have the same print info.
    // Post-comments : What is the big deal anyway.
    bool check_variable_compatibility(var_info const* f1) const
    {
        return (f1 == f);
    }

    // access the ith coefficient
    Rational& operator[](int i);
    // const reference to the same
    Rational operator()(int i) const;

    // access members
    int get_dim() const;
    var_info* get_info() const;

    // disabled
    // vector<Rational> & get_array();

    // is this a constant?
    bool is_constant() const;

    // zero?
    bool is_zero() const;

    // destructor
    ~LinExpr();

    // scale this up to make all coeffs integer.
    // for use in converting to Linear_Expression.
    int get_denominator_lcm() const;
    int get_numerator_gcd() const;

    // Is it the case that factor * l1 = this for some factor.
    // output parameter factor.
    bool equiv(LinExpr const& l1, Rational& factor) const;

    // convert to PPL representation.
    Linear_Expression to_lin_expression() const;
    Constraint get_constraint(int ineq_type) const;

    // with generator g providing valuations, eval.
    Rational evaluate(Generator const& g);
    // pretty print.
    void print(ostream& os) const;
    // print in array invariant format
    void print_in_arrinv() const;
};

// to print my beautiful Lin Exprs
ostream& operator<<(ostream& os, LinExpr const& expr);

// more scaling operators.
LinExpr operator*(Rational const& i, LinExpr const& p1);
LinExpr operator*(LinExpr const& p1, Rational const& i);
LinExpr operator*(int i, LinExpr const& p1);

#endif
