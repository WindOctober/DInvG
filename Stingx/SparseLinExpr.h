
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

#ifndef D__SPARSE_LIN_EXPR__H_
#define D__SPARSE_LIN_EXPR__H_

#include <iostream>
#include <map>
#include <utility>

#include "LinExpr.h"
#include "Rational.h"
#include "global_types.h"
#include "ppl.hh"
#include "var-info.h"

using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;

// IRMap stands for CoefficientRationalMap
// IRMapIterator ....
// IRPair is a pair of int, Rational
// ItBPair is a pair of an iterator to a map entry and a boolean

typedef map<int, Rational> IRMap;
typedef map<int, Rational>::iterator IRMapIterator;
typedef pair<int, Rational> IRPair;
typedef pair<IRMap::iterator, bool> ItBPair;

class SparseLinExpr {
   protected:
    //
    // This is a implementation of the sparse linear expressions
    // This is meant for use when the number of variables is overwhelmingly
    // large and each expression uses a much smaller number of variables
    //
    // Each operation is going to be costlier. Here are the members
    //  1. n_ is the number of variables (This could be varied dynamically).
    //  2. m_ is the map that maps a coefficient i to a rational.
    //     Semantics: If m_(i) is not found, then zero should be returned
    //  3. f_ is a var_info that has the printing information for the variables
    //  4. count  (Added for the sake of maintaining consistency with an older
    //  implementation).
    //

    int n_;

    var_info* f_;

    IRMap m_;

    int count_;
    bool info_set_;
    void clear_out();

    void initialize(int n, var_info* f);  // will call off the use of this.

    bool _class_invariant_check() const;

    bool flag_;  // just provide a way to set a flag for applications

   public:
    SparseLinExpr();

    SparseLinExpr(int n, var_info* f);

    SparseLinExpr(LinExpr const& ll);

    void init_set(int n, var_info* f) { initialize(n, f); }

    void add_coefficient(int index, Rational const& what);

    void set_coefficient(int index, Rational const& what);

    void set_coefficient(int index, int what)
    {
        set_coefficient(index, Rational(what, 1));
    }

    void subtract_coefficient(int index, Rational const& what);

    void subtract_scaled(SparseLinExpr const& x, Rational const& scale);
    void add_scaled(SparseLinExpr const& x, Rational const& scale);

    Rational get_coefficient(int index) const;

    SparseLinExpr operator+(SparseLinExpr const& p1) const;  // Addition
    SparseLinExpr& operator+=(SparseLinExpr const& p1);

    SparseLinExpr operator-(SparseLinExpr const& p1) const;

    SparseLinExpr& operator-=(SparseLinExpr const& p1);  // Addition to self

    SparseLinExpr& operator=(SparseLinExpr const& p1);  // Assignment

    SparseLinExpr& operator*=(int i);
    SparseLinExpr& operator*=(Rational const& i);

    bool operator==(SparseLinExpr const& t) const;

    int get_count() const { return count_; }

    int reset_count()
    {
        int t = count_;
        count_ = 0;
        return t;
    }

    int count_up() { return count_++; }
    int count_down() { return count_--; }

    bool check_variable_compatibility(var_info const* f1) const
    {
        return (f1 == f_);
    }

    /*
     * // Do not call this. This is just there for compatibility sake
     * Rational & operator[](int i); // call will cause a precondition violation
     *
     */

    Rational operator()(int i) const;

    int get_dim() const { return n_; }
    var_info* get_info() const { return f_; }

    IRMap const& get_map() const { return m_; }

    // is the expression a constant? Is it a zero?
    // could require a search on the entire expression

    bool is_constant() const;
    bool is_zero() const { return (m_.size() == 0); }

    // These are meant for factorizing out the common factors
    int get_denominator_lcm() const;

    int get_numerator_gcd() const;

    // is there a factor such that this expression
    // is equivalent to l1 upto that multiplying factor?

    bool equiv(SparseLinExpr const& l1, Rational& factor) const;

    // convert to PPL format
    Linear_Expression to_lin_expression() const;

    // obtain the constraint correspondint to the ineq_type . see global_types.h
    // for details
    Constraint get_constraint(int ineq_type) const;

    // evaluate the generator which provides the values for the variables

    Rational evaluate(Generator const& g) const;

    // do a merge by offsetting ex2 variables
    void merge_assign(SparseLinExpr& ex2);

    // convert this into a lin expression, scale that by scale_fact and offset
    // the variables by adding offset. Add the result to ll

    void add_to_lin_expression(Linear_Expression& ll, int scale_fact = 1,
                               int offset = 0) const;

    void print(ostream& os) const;

    int obtain_largest_coefficient() const
    {
        if (is_zero()) {
            cerr << "Fatal Error in SparseLinExpr::obtain_largest_coefficient"
                 << endl
                 << "called on a zero expression" << endl;
            exit(1);
        }

        return (*(m_.rbegin())).first;
    }

    // functions for setting/getting flags
    bool get_flag() const { return flag_; }

    bool set_flag(bool what)
    {
        bool t = flag_;
        flag_ = what;
        return t;
    }

    // variables of index >= k that occur in the linear expression
    // should be added to the set what
    void occurring_variables(set<int>& what, int k = 0) const;

    void add_variables_in_front(
        int n1);  // add n1 variables to the front of the expression

    void add_variables_in_back(
        int n1);  // add n1 variables to the back of the expression

    void make_unprintable() { info_set_ = false; }

    bool is_printable() const { return info_set_; }

    // replace the old var-info with the new varinfo

    void replace_var_info_with(var_info* ninfo);

    Rational dot_product(SparseLinExpr const& what) const;
};

ostream& operator<<(
    ostream& os, SparseLinExpr const& expr);  // to print my beautiful Lin Exprs

SparseLinExpr operator*(Rational const& i, SparseLinExpr const& p1);

SparseLinExpr operator*(SparseLinExpr const& p1, Rational const& i);

SparseLinExpr operator*(int i, SparseLinExpr const& p1);

SparseLinExpr operator*(SparseLinExpr const& p1, int i);

#endif
