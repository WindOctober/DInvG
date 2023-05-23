
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
 * Filename: DisequalityStore.cc
 * Author: Sriram Sankaranarayanan<srirams@theory.stanford.edu>
 * Comments: A disequality + inequality constraint store for the multiplier
 * variables operations to be supported are the addition of equalities,
 * inequalities, disequalities and linear transformation operations. Inefficient
 * implementation. To be rectified depending on performance criteria. Important
 * Note: ALL VARIABLES ARE ASSUMED TO BE POSITIVE (>=0)
 *
 * Post-comments: Looks like this is not a bottleneck. Will keep it.
 * Copyright: Please see README file.
 */

#ifndef __DISEQ_STORE__H_
#define __DISEQ_STORE__H_
#include <iostream>
#include <vector>

#include "LinTransform.h"
#include "MatrixStore.h"
#include "PolyStore.h"
#include "PolyUtils.h"
#include "Rational.h"
#include "SparseLinExpr.h"
#include "global_types.h"
#include "ppl.hh"
#include "var-info.h"

using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;

class DisequalityStore {
   private:
    /*
     * Class Members:
     *    vp = a vector of disequalities.
     *    ineq_exprs = the inequalities
     *    vars_num = dimensionality
     *    info= information for printing
     *   incon = flag signifying inconsistent
     */

    vector<Linear_Expression>*
        vp;  // The vector of linear expressions  treated as disequalities

    C_Polyhedron* ineq_exprs;  // The inequalities of the system

    int vars_num;        // the dimensionality  of the system
    var_info* info;  // The information about variables

    bool incon;

    void initialize(int vars_num, var_info* info);
    // check for consistency
    void check_consistent();

   public:
    DisequalityStore(int vars_num, var_info* info);
    ~DisequalityStore();

    // add a constraint
    // ineq_type has been #defined in global_types.h

    void add_constraint(SparseLinExpr const& p, int ineq_type);

    // force set the inequalities to p
    void set_inequalities(C_Polyhedron const* p);
    // force set the disequalities to those in vp
    void set_disequalities(vector<SparseLinExpr>* vp);
    // same as above support different format for expressions
    void set_disequalities(vector<Linear_Expression> const* vp);

    bool is_consistent() const;

    // check if the polyhedron t is consistent with the disequalities.

    // algorithm : for each disequality e<>0 check if t \models e==0
    // if this happens then t is inconsistent. else t /\ disequalities here
    // are consistent.

    bool check_consistent(C_Polyhedron& t);

    // the dimension
    int get_dimension() const;
    // the var_info
    const var_info* get_var_info() const;
    // cover function for print
    void print_constraints(ostream& in) const;

    // some utility functions for making life easier
    // add l == 0 with l in the transform representation
    bool add_transform(LinTransform const& l);
    // add l>=0
    bool add_transform_inequality(LinTransform const& l);
    // add l<> 0
    bool add_transform_negated(LinTransform const& l);
    // Check if adding l==0 will create an inconsistent store.
    bool check_status_equalities(LinTransform& l);

    // clone this store completely
    // Post comment- I suck. Should have avoided pointers.
    DisequalityStore* clone() const;
};

ostream& operator<<(ostream& in, DisequalityStore const& lambda_store);

#endif
