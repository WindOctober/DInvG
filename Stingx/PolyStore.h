
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
 * Filename: PolyStore
 * Author: Sriram Sankaranarayanan
 * Comments: A inequality constraint solver implemented through PPL.
 *           Consolidation routines provided.
 * Post-comments: Old implementation.
 * Copyright: see README file for details
 */

#ifndef __POLY_STORE__H_
#define __POLY_STORE__H_

// A store for polyhedral constraints
#include <iostream>
#include <vector>

#include "MatrixStore.h"
#include "Rational.h"
#include "SparseLinExpr.h"
#include "global_types.h"
#include "ppl.hh"
#include "var-info.h"

using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;

class PolyStore {
   private:
    // Post-Comments: I am no longer sure what trivial_poly is doing here.
    // Post-Post-Comments: Keep trivial_poly. It is necessary.
    // p = The polyhedron central to the constraint store
    C_Polyhedron *p, *trivial_poly;

    // printing information
    var_info* info;
    // vector<Variable *> * v;
    int varsNum;  // The dimensions

    void initialize(int varsNum, var_info* info);
    void make_trivial_polyhedron();

   public:
    PolyStore(int varsNum, var_info* info);
    ~PolyStore();

    // add constraints

    void add_constraint(SparseLinExpr const& p, int ineq_type);
    void add_constraint(Constraint const& cc);

    bool is_consistent() const;  // Check if the system is satisfiable
    bool is_trivial() const;     // Check if the system is trivial

    // push the linear equalities
    // part of the store into the Matrix Store m
    void extract_linear_part(MatrixStore& m) const;

    // push the
    // constraints in the linear store into the polyhedron
    void add_linear_store(MatrixStore const& m);

    // access stuff
    const C_Polyhedron& get_nnc_poly_reference() const;
    C_Polyhedron& getPolyRef();
    var_info* get_var_info() const;
    int getDim() const;

    // test containment
    bool contained(C_Polyhedron* pp);

    // clone
    PolyStore* clone() const;

    // This line of research was abandoned. But keep it anyway.
    void collect_generators(Generator_System& g);
    Generator_System minimized_generators();
};

ostream& operator<<(ostream& info, PolyStore const& p);

#endif
