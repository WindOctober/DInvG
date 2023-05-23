
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

#include "PolyStore.h"

#include <iostream>
#include <ppl.hh>
#include <vector>

#include "MatrixStore.h"
#include "Rational.h"
#include "SparseLinExpr.h"
#include "var-info.h"

extern C_Polyhedron* trivial;

void PolyStore::initialize(int vars_num, var_info* info) {
    this->vars_num = vars_num;
    this->info = info;
    // Build a polyhedron with a space dimension vars_num
    p = new C_Polyhedron(vars_num);
    make_trivial_polyhedron();
}

void PolyStore::add_constraint(SparseLinExpr const& l, int ineq_type) {
    // Build a linear expression corresponding to the expression p
    Constraint cc = l.get_constraint(ineq_type);
    p->add_constraint(cc);
}

void PolyStore::add_constraint(Constraint const& cc) {
    p->add_constraint(cc);
}

PolyStore::PolyStore(int vars_num, var_info* info) {
    initialize(vars_num, info);
}

bool PolyStore::is_consistent() const {
    return !(p->is_empty());
}

void PolyStore::make_trivial_polyhedron() {
    // Construct the zero polyhedron on vars_num dimensions
    // Question: Does PPL have a routine to do this?

    C_Polyhedron* trivial_poly = new C_Polyhedron(vars_num, EMPTY);
    int i;
    Linear_Expression l;
    for (i = 0; i < vars_num; i++) {
        Variable v(i);
        l = l + 0 * v;
    }
    // add the zero generator to the empty polyhedron
    Generator g = Generator::point(l, 1);
    trivial_poly->add_generator(g);
    return;
}

bool PolyStore::is_trivial() const {
    // check that that the origin is the only point in the polyhedron
    return trivial->contains(*p);
}

void PolyStore::extract_linear_part(MatrixStore& m) const {
    // First obtain the set of constraints in the polyhedron
    Constraint_System cs = p->minimized_constraints();
    // extract the constraints from the polyhedron
    // iterator to explore the obtained constraint system
    Constraint_System::const_iterator vi;

    // stuff
    SparseLinExpr l(vars_num, info);
    Coefficient t;
    int i;
    bool nonzero;

    // iterate through the constraints
    for (vi = cs.begin(); vi != cs.end(); vi++) {
        Constraint cc = (*vi);

        nonzero = false;
        if (cc.is_equality()) {
            // Convert the constraint cc into a linear expression to be added
            // into the matrix store

            // conversion to a SparseLinear_Expression starts here..

            // Post-Comments: TODO-- why cannot I add a constructor
            // SparseLinExpr(Linear_Expression) Post-post-comments: Should keep
            // SparseLinExpr PPL free?

            // iterate through coefficients
            for (i = 0; i < vars_num; i++) {
                Coefficient t = cc.coefficient(Variable(i));
                if (!t.fits_sint_p()) {
                    cout << "Error in PolyStore::extract_linear_part-- gmp "
                            "integer "
                            "overflow"
                         << endl;
                    exit(1);
                }

                l.set_coefficient(i, (int)t.get_si());
                if (l(i) == 0) {
                } else {
                    nonzero = true;
                }
            }

            t = cc.inhomogeneous_term();
            if (!t.fits_sint_p()) {
                cout << "Error in PolyStore::extract_linear_part-- gmp integer "
                        "overflow"
                     << endl;
                exit(1);
            }
            l.set_coefficient(vars_num, (int)t.get_si());
            // bizarre code.. implement rational !=0 operator please.
            if (!(l(vars_num) == 0)) {
                nonzero = true;
            }

            // add non-zero constraint into the matrix
            if (nonzero) {
                m.add_constraint(l);
            }

        }  // if not equality then nothing to be done!
    }

    // return
}

void PolyStore::add_linear_store(MatrixStore const& m) {
    // Take each constraint from the store and
    // add to the polyhedron
    Constraint_System cs = m.to_constraint_system();
    p->add_constraints(cs);
}

int PolyStore::get_dimension() const {
    return vars_num;
}

const C_Polyhedron& PolyStore::get_nnc_poly_reference() const {
    return (*p);
}

C_Polyhedron& PolyStore::get_poly_reference() {
    return (*p);
}

var_info* PolyStore::get_var_info() const {
    return info;
}

ostream& operator<<(ostream& os, PolyStore const& p) {
    // print the contents of p into os
    int vars_num = p.get_dimension();

    os << "├ Polyhedral Constraint Store of Dimension " << vars_num << endl;

    C_Polyhedron pp = p.get_nnc_poly_reference();
    Constraint_System cs = pp.minimized_constraints();
    var_info* info = p.get_var_info();

    int i;
    Coefficient t;

    Constraint_System::const_iterator vi;
    SparseLinExpr l(vars_num, info);

    for (vi = cs.begin(); vi != cs.end(); ++vi) {
        Constraint cc = *vi;

        for (i = 0; i < vars_num; i++) {
            t = cc.coefficient(Variable(i));
            l.set_coefficient(i, (int)t.get_si());
        }

        t = cc.inhomogeneous_term();
        l.set_coefficient(i, (int)t.get_si());

        os << "├ ";
        os << l;  // Print the linear constraint

        if (cc.is_equality())
            os << " =  0 ";
        else if (cc.is_nonstrict_inequality())
            os << " >= 0 ";
        else
            os << " > 0  ";

        os << endl;
    }

    os << "├ End Polyhedral Constraint Store Listing" << endl;
    return os;
}

PolyStore* PolyStore::clone() const {
    // create a new cloned polystore
    PolyStore* ret = new PolyStore(vars_num, info);
    // now extract the constraints from p
    Constraint_System cs =
        p->minimized_constraints();  // extract the constraints
                                     // from the polyhedron
    Constraint_System::const_iterator
        vi;  // iterator to explore the obtained constraint system

    for (vi = cs.begin(); vi != cs.end(); vi++) {
        ret->add_constraint((*vi));
    }

    return ret;
}

void PolyStore::collect_generators(Generator_System& g) {
    // just strip the generators off p and insert them in g
    Generator_System g1 = p->minimized_generators();
    Generator_System::const_iterator vi;
    for (vi = g1.begin(); vi != g1.end(); vi++) {
        g.insert(*vi);
    }
    return;
}

Generator_System PolyStore::minimized_generators() {
    Generator_System g, g1 = p->minimized_generators();
    Generator_System::const_iterator vi;
    for (vi = g1.begin(); vi != g1.end(); vi++)
        g.insert(Generator((*vi)));  // use a copy constructor to clone
    return g;
}

bool PolyStore::contained(C_Polyhedron* pp) {
    return pp->contains(*p);
}

PolyStore::~PolyStore() {}
