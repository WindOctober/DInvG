
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
    //  1. varNum is the number of variables (This could be varied dynamically).
    //  2. map_ration is the map that maps a coefficient i to a rational.
    //     Semantics: If map_ration(i) is not found, then zero should be returned
    //  3. varInfo is a var_info that has the printing information for the variables
    //  4. count  (Added for the sake of maintaining consistency with an older
    //  implementation).
    //

    int varNum;

    var_info* varInfo;

    IRMap map_ration;

    int count_;
    bool info_set_;
    void clear_out();

    void initialize(int n, var_info* info);  // will call off the use of this.

    bool _class_invariant_check() const;

    bool flag_;  // just provide a way to set a flag for applications

   public:
    SparseLinExpr();

    SparseLinExpr(int n, var_info* info);

    SparseLinExpr(LinExpr const& ll);

    void init_set(int n, var_info* info) { initialize(n, info); }

    void add_coefficient(int index, Rational const& what);

    void setCoefficient(int index, Rational const& what);

    void setCoefficient(int index, int what) {
        setCoefficient(index, Rational(what, 1));
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

    int getCount() const { return count_; }

    int resetCounter() {
        int t = count_;
        count_ = 0;
        return t;
    }

    int count_up() { return count_++; }
    int count_down() { return count_--; }

    bool check_variable_compatibility(var_info const* f1) const {
        return (f1 == varInfo);
    }

    /*
     * // Do not call this. This is just there for compatibility sake
     * Rational & operator[](int i); // call will cause a precondition violation
     *
     */

    Rational operator()(int i) const;

    int getDim() const { return varNum; }
    var_info* getInfo() const { return varInfo; }

    IRMap const& get_map() const { return map_ration; }

    // is the expression a constant? Is it a zero?
    // could require a search on the entire expression

    bool is_constant() const;
    bool isZero() const { return (map_ration.size() == 0); }

    // These are meant for factorizing out the common factors
    int getDenLcm() const;

    int getNumGcd() const;

    // is there a factor such that this expression
    // is equivalent to l1 upto that multiplying factor?

    bool equiv(SparseLinExpr const& l1, Rational& factor) const;

    // convert to PPL format
    Linear_Expression toLinExpression() const;

    // obtain the constraint correspondint to the ineqType . see global_types.h
    // for details
    Constraint get_constraint(int ineqType) const;

    // evaluate the generator which provides the values for the variables

    Rational evaluate(Generator const& g) const;

    // do a merge by offsetting ex2 variables
    void merge_assign(SparseLinExpr& ex2);

    // convert this into a lin expression, scale that by scale_fact and offset
    // the variables by adding offset. Add the result to ll

    void print(ostream& os) const;

    void make_unprintable() { info_set_ = false; }

    bool is_printable() const { return info_set_; }

};

ostream& operator<<(
    ostream& os,
    SparseLinExpr const& expr);  // to print my beautiful Lin Exprs

SparseLinExpr operator*(Rational const& i, SparseLinExpr const& p1);

SparseLinExpr operator*(SparseLinExpr const& p1, Rational const& i);

SparseLinExpr operator*(int i, SparseLinExpr const& p1);

SparseLinExpr operator*(SparseLinExpr const& p1, int i);

#endif
