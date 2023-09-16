
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

#include "DisequalityStore.h"

void DisequalityStore::initialize(int varsNum, var_info* info) {
    //
    // initialize the store.
    // with varsNum dimensions and var-info info
    // Question to self: why on earth could this not have been written in the
    // constructor itself. Learnt costly lesson :-)
    //

    this->varsNum = varsNum;
    this->info = info;
    polys = new vector<Linear_Expression>();
    ineqExprs = new C_Polyhedron(varsNum, UNIVERSE);

    // Automatically set all the variables to be positive
    // This is not part of the general semantics for this class
    // but this is useful anyway.

    int i;
    for (i = 0; i < varsNum; i++)
        ineqExprs->add_constraint(Variable(i) >= 0);

    // initial store is consistent
    ConsistencyFlag = false;
}

DisequalityStore::DisequalityStore(int varsNum, var_info* info) {
    initialize(varsNum, info);
}

void DisequalityStore::checkConsistent() {
    if (ConsistencyFlag)
        return;
    // first check if ineqExprs is non-empty
    if (ineqExprs->is_empty()) {
        ConsistencyFlag = true;
        return;
    }
    Poly_Con_Relation includeRel = Poly_Con_Relation::is_included(), curRel(includeRel);

    vector<Linear_Expression>::iterator it = polys->begin();

    // iterate through polys
    for (it = polys->begin(); it != polys->end(); ++it) {
        // What is the relation between the ineqExprs and (*it)==0
        curRel = ineqExprs->relation_with((*it) == 0);
        if (curRel == includeRel) {
            ConsistencyFlag = true;
            break;
        }
    }
}

bool DisequalityStore::checkConsistent(C_Polyhedron& poly) {
    // just do the same as in checkConsistent()..
    // two changes.. 1. do not set ineqExprs
    //               2. do not use ineqExprs member
    //  Post comment== I could have factored checkConsistent() into this. I
    //  suck

    // first check if poly is non-empty
    if (poly.is_empty()) {
        return false;
    }

    Poly_Con_Relation rel1 = Poly_Con_Relation::is_included(), rel(rel1);
    vector<Linear_Expression>::iterator it = polys->begin();

    for (it = polys->begin(); it != polys->end(); ++it) {
        // What is the relation between the ineqExprs and (*it)==0
        rel = poly.relation_with((*it) == 0);

        if (rel == rel1) {
            return false;
        }
    }

    return true;
}

void DisequalityStore::add_constraint(SparseLinExpr const& p, int ineq_type) {
    // add a constraint

    // if inconsistent .. then nothing to be done here.
    if (ConsistencyFlag)
        return;

    // if the inequality is a disequality .. puch it into
    // polys after converting it to a linear expression a la PPL

    if (ineq_type == TYPE_DIS) {
        polys->push_back(p.to_lin_expression());
    } else {
        ineqExprs->add_constraint(p.get_constraint(ineq_type));
    }

    // check if the whole new mess is consistent
    checkConsistent();
    // return.
}

bool DisequalityStore::is_consistent() const {
    // not inconsistent
    return !ConsistencyFlag;
}

int DisequalityStore::getDim() const {
    return varsNum;
}

const var_info* DisequalityStore::get_var_info() const {
    return info;
}

void DisequalityStore::print_constraints(ostream& in) const {
    // print the whole thing out using ostream

    if (ConsistencyFlag) {
        in << " Inconsistent Store" << endl;

#ifdef __DEBUG__D_
        in << "Test Message--" << endl;
        print_polyhedron(in, *ineqExprs, info);
        vector<Linear_Expression>::iterator it;

        for (it = polys->begin(); it < polys->end(); it++) {
            print_lin_expression(in, (*it), info);
            in << " <> 0" << endl;
        }
        in << "Test message ends" << endl;
#endif
        return;
    }

    in << "├ Consistent Store" << endl;

    // print the polyhedron

    print_polyhedron(in, *ineqExprs, info);

    vector<Linear_Expression>::iterator it;
    // print the disequalities
    for (it = polys->begin(); it < polys->end(); it++) {
        in << "├ ";
        print_lin_expression(in, (*it), info);
        in << " <> 0" << endl;
    }
    // done

    in << endl;
}

bool DisequalityStore::addTransform(LinTransform const& l) {
    // add l==0 after changing l to a linear expression a la PPL
    Linear_Expression l1 = l.to_lin_expression();
    ineqExprs->add_constraint(l1 == 0);
    checkConsistent();
    return ConsistencyFlag;
}

bool DisequalityStore::add_transform_inequality(LinTransform const& l) {
    // a la PPL
    Linear_Expression l1 = l.to_lin_expression();
    // add l>=0
    ineqExprs->add_constraint(l1 >= 0);
    checkConsistent();
    return ConsistencyFlag;
}

bool DisequalityStore::add_transform_negated(LinTransform const& l) {
    // a la PPL
    Linear_Expression l1 = l.to_lin_expression();
    // add l1<> 0
    polys->push_back(l1);
    checkConsistent();
    return ConsistencyFlag;
}

ostream& operator<<(ostream& in, DisequalityStore const& disequalStore) {
    // print
    disequalStore.print_constraints(in);
    return in;
}

DisequalityStore* DisequalityStore::clone() const {
    // clone the disequality store
    // create a new one
    DisequalityStore* ret = new DisequalityStore(varsNum, info);
    // force set inequalities to ineqExprs (by cloning ineqExprs)

    ret->set_inequalities(ineqExprs);
    // clone polys and force set
    ret->set_disequalities(polys);

    // recheck the consistency of ret or dump core
    ret->checkConsistent();

    // return the clone
    return ret;
}

void DisequalityStore::set_inequalities(C_Polyhedron const* p) {
    // force set the inequalities
    // Post comment: Why not use the copy constructor?

    // iterate through constraints

    Constraint_System cs = p->minimized_constraints();
    Constraint_System::const_iterator it;

    // add the constraints one by one
    for (it = cs.begin(); it != cs.end(); it++)
        ineqExprs->add_constraint(*it);

    // unnecessary actually.. but will do it anyways
    checkConsistent();
    return;
}

void DisequalityStore::set_disequalities(vector<SparseLinExpr>* polys) {
    // each sparselinexpr requires conversion before addition

    vector<SparseLinExpr>::iterator it;
    // add the constraints one by one
    for (it = polys->begin(); it < polys->end(); it++)
        add_constraint((*it), TYPE_DIS);

    checkConsistent();
}

void DisequalityStore::set_disequalities(vector<Linear_Expression> const* vp1) {
    // a different format.. just directly clone

    // vector<Linear_Expression>::iterator it;
    delete (polys);
    polys = new vector<Linear_Expression>(*vp1);

    checkConsistent();
}

bool DisequalityStore::check_status_equalities(LinTransform& lt) {
    // check if adding lt==0 will create inconsistencies
    // First add lt==0 to the polyhedron and then check consistency

    // create a polyhedron poly with ineqExprs /\ l1 ==0

    C_Polyhedron poly(*ineqExprs);

    Linear_Expression l1 = lt.to_lin_expression();
    poly.add_constraint(l1 == 0);

    // check if things will remain consistent.
    return checkConsistent(poly);
}

DisequalityStore::~DisequalityStore() {
    // the destructor
    delete (polys);
}
