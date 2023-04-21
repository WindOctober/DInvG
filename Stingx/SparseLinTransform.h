
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
 * Filename: SparseLinTransform
 * Author: Sriram Sankaranarayanan<srirams@theory.stanford.edu>
 * Comments: Same as LinExpr. The coefficients are understood to be multiplier
 * variables here. Post-Comments: I am still using LINTRANSFORM instead of this.
 * Copyright: Please see README file.
 */

//
#ifndef D__SPARSE_LIN_TRANSFORM__H_
#define D__SPARSE_LIN_TRANSFORM__H_

//
// this represents a collection of sparse lin exprs
// this will represent a variable that is written as a transformation
// in terms of the other system variables.
// As a rule I will write the lowest/highest ordered variable in terms
// of the other variables
//

#include <set>
#include <utility>
#include <vector>

#include "Rational.h"
#include "SparseLinExpr.h"
#include "ppl.hh"
#include "var-info.h"
using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;

struct ltstr {
    bool operator()(int i1, int i2) { return i1 > i2; }
};

typedef map<int, SparseLinExpr, ltstr> TRMap;
typedef pair<int, SparseLinExpr> TRPair;

class SparseLinTransform {
   private:
    //
    // This class represents a system of homogenous
    // linear transformations of the form
    // x_i -> a_1 x_1 + ... + a_{i-1} x_{i-1}
    //
    // The representation of a_1 x_1 + ...+.. is by a SparseLinExpr
    // So such a system will be represented by a map that maps
    // i into the required linear expression
    //

    // members are

    int _n;    // the number of variables
    TRMap _m;  // the map itself

   public:
    // a simple constructor
    SparseLinTransform(int n) : _n(n) {}

    void normal_form_assign(SparseLinExpr& s) const;
    SparseLinExpr normal_form(SparseLinExpr const& s) const;
    void add_expression(SparseLinExpr const& s);

    bool is_variable_dependent(int i) { return (_m.find(i) == _m.end()); }
};

#endif
