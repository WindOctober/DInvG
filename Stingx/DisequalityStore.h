
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
     *    disEquals = a vector of disequalities.
     *    ineqExprs = the inequalities
     *    varsNum = dimensionality
     *    info= information for printing
     *   InConsistency = flag signifying inconsistent
     */

    vector<Linear_Expression>* disEquals;  // The vector of linear expressions  treated as disequalities

    C_Polyhedron* ineqExprs;  // The inequalities of the system

    int varsNum;        // the dimensionality  of the system
    var_info* info;  // The information about variables

    bool InConsistency;

    void initialize(int varsNum, var_info* info);
    // check for consistency
    void checkConsistent();

   public:
    DisequalityStore(int varsNum, var_info* info);
    ~DisequalityStore();

    // add a constraint
    // ineqType has been #defined in global_types.h

    void addConstraint(SparseLinExpr const& p, int ineqType);

    // force set the inequalities to p
    void setIneqPoly(C_Polyhedron const* p);
    // force set the disequalities to those in disEquals
    void setDisEquals(vector<SparseLinExpr>* disEquals);
    // same as above support different format for expressions
    void setDisEquals(vector<Linear_Expression> const* disEquals);

    bool isConsistent() const;

    // check if the polyhedron t is consistent with the disequalities.

    // algorithm : for each disequality e<>0 check if t \models e==0
    // if this happens then t is inconsistent. else t /\ disequalities here
    // are consistent.

    bool checkConsistent(C_Polyhedron& t);

    // the dimension
    int getDim() const;
    // the var_info
    const var_info* getInfo() const;
    // cover function for print
    void printConstraints(ostream& in) const;

    // some utility functions for making life easier
    // add l == 0 with l in the transform representation
    bool addTransform(LinTransform const& l);
    // add l>=0
    bool addIneqTransform(LinTransform const& l);
    // add l<> 0
    bool addNegTransform(LinTransform const& l);
    // Check if adding l==0 will create an inconsistent store.
    bool check_status_equalities(LinTransform& l);

    // clone this store completely
    // Post comment- I suck. Should have avoided pointers.
    DisequalityStore* clone() const;
};

ostream& operator<<(ostream& in, DisequalityStore const& LambdaStore);

#endif
