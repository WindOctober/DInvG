
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
 * Filename: MatrixStore
 * Author: Sriram Sankaranarayanan
 * Comments: A equality constraint solver implements gaussian algorithm.
 * Simplification and consolidation routines provided. Post-comments: Old
 * implementation. Copyright: see README file for details
 */

#ifndef __MATRIX__H_
#define __MATRIX__H_

#include <Rational.h>

#include "SparseLinExpr.h"
#include "funcs.h"
#include "global_types.h"
#include "ppl.hh"
#include "var-info.h"  // The information on variable names
using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;

class MatrixStore {
   private:
    // Represent the system $A x =b$, where A is a rational m x n matrix and
    //  b is a mx 1 vector
    //
    // We need to use this as a "Constraint Store"
    // Chief functionalities to be handled are
    // 1. Initialize with a fixed number of variables
    // 2. Add constraints when they come in and detect if the
    //    constraint is satisfiable w.r.t the current store before adding
    // 3. Simplify a given expression into a new expression

    // The matrix A|b is an augmented matrix
    // such that A is kept in rref form..
    // It means Ax -b =0
    // no need to have more than n rows!

    Rational** mat;
    int n;
    var_info* f;
    bool consistent;
    void initialize(int n, var_info* f);
    void zero_out();

   public:
    MatrixStore();

    MatrixStore(int n, var_info* f);  // initialize the store

    void init_set(int n, var_info* f);

    int simplify(SparseLinExpr& expression) const;  // Simplify an expression

    // add a constraint from a SparseLinExpr
    bool add_constraint(SparseLinExpr& expression);

    int get_dim() const;
    var_info* get_info() const;
    Rational** get_matrix() const;
    void print() const;
    Rational& operator()(int i, int j);
    // some basic gaussian elimination routines
    void back_substitute(int l);

    // accessors
    bool is_consistent() const;
    void set_consistent(bool c);

    ~MatrixStore();

    // Convert to PPL representation
    Constraint_System to_constraint_system() const;
    // clone
    MatrixStore* clone() const;
};

ostream& operator<<(ostream& os, MatrixStore const& m);
#endif
