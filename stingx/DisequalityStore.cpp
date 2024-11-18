
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
    this->varsNum = varsNum;
    this->info = info;
    disEquals = new vector<Linear_Expression>();
    ineqExprs = new C_Polyhedron(varsNum, UNIVERSE);
    int i;
    for (i = 0; i < varsNum; i++)
        ineqExprs->add_constraint(Variable(i) >= 0);
    InConsistency = false;
}

DisequalityStore::DisequalityStore(int varsNum, var_info* info) {
    initialize(varsNum, info);
}

void DisequalityStore::checkConsistent() {
    if (InConsistency)
        return;
    // first check if ineqExprs is non-empty
    if (ineqExprs->is_empty()) {
        InConsistency = true;
        return;
    }
    Poly_Con_Relation includeRel = Poly_Con_Relation::is_included(), curRel(includeRel);

    vector<Linear_Expression>::iterator it = disEquals->begin();

    // iterate through disEquals
    for (it = disEquals->begin(); it != disEquals->end(); ++it) {
        // What is the relation between the ineqExprs and (*it)==0
        curRel = ineqExprs->relation_with((*it) == 0);
        if (curRel == includeRel) {
            InConsistency = true;
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
    vector<Linear_Expression>::iterator it = disEquals->begin();

    for (it = disEquals->begin(); it != disEquals->end(); ++it) {
        // What is the relation between the ineqExprs and (*it)==0
        rel = poly.relation_with((*it) == 0);

        if (rel == rel1) {
            return false;
        }
    }

    return true;
}

void DisequalityStore::addConstraint(SparseLinExpr const& p, int ineqType) {
    if (InConsistency)
        return;
    // if the inequality is a disequality .. puch it into
    // disEquals after converting it to a linear expression a la PPL
    if (ineqType == TYPE_DIS) {
        disEquals->push_back(p.toLinExpression());
    } else {
        ineqExprs->add_constraint(p.get_constraint(ineqType));
    }
    checkConsistent();
    return;
}

bool DisequalityStore::isConsistent() const {
    // not inconsistent
    return !InConsistency;
}

int DisequalityStore::getDim() const {
    return varsNum;
}

const var_info* DisequalityStore::getInfo() const {
    return info;
}

void DisequalityStore::printConstraints(ostream& in) const {
    // print the whole thing out using ostream

    if (InConsistency) {
        in << " Inconsistent Store" << endl;
        return;
    }

    in << "├ Consistent Store" << endl;
    printPolyhedron(in, *ineqExprs, info);
    vector<Linear_Expression>::iterator it;
    // print the disequalities
    for (it = disEquals->begin(); it < disEquals->end(); it++) {
        in << "├ ";
        print_lin_expression(in, (*it), info);
        in << " <> 0" << endl;
    }
    in << endl;
    return;
}

bool DisequalityStore::addTransform(LinTransform const& l) {
    // add l==0 after changing l to a linear expression a la PPL
    Linear_Expression l1 = l.toLinExpression();
    ineqExprs->add_constraint(l1 == 0);
    checkConsistent();
    return InConsistency;
}

bool DisequalityStore::addIneqTransform(LinTransform const& l) {
    Linear_Expression l1 = l.toLinExpression();
    ineqExprs->add_constraint(l1 >= 0);
    checkConsistent();
    return InConsistency;
}

bool DisequalityStore::addNegTransform(LinTransform const& l) {
    Linear_Expression l1 = l.toLinExpression();
    disEquals->push_back(l1);
    checkConsistent();
    return InConsistency;
}

ostream& operator<<(ostream& in, DisequalityStore const& LambdaStore) {
    LambdaStore.printConstraints(in);
    return in;
}

DisequalityStore* DisequalityStore::clone() const {
    DisequalityStore* ret = new DisequalityStore(varsNum, info);
    ret->setIneqPoly(ineqExprs);
    ret->setDisEquals(disEquals);
    ret->checkConsistent();
    return ret;
}

void DisequalityStore::setIneqPoly(C_Polyhedron const* p) {
    Constraint_System cs = p->minimized_constraints();
    for (auto it = cs.begin(); it != cs.end(); it++)
        ineqExprs->add_constraint(*it);
    checkConsistent();
    return;
}

void DisequalityStore::setDisEquals(vector<SparseLinExpr>* disEquals) {
    for (auto it = disEquals->begin(); it < disEquals->end(); it++)
        addConstraint((*it), TYPE_DIS);
    checkConsistent();
}

void DisequalityStore::setDisEquals(vector<Linear_Expression> const* vp1) {
    delete (disEquals);
    disEquals = new vector<Linear_Expression>(*vp1);
    checkConsistent();
}

bool DisequalityStore::check_status_equalities(LinTransform& lt) {
    // check if adding lt==0 will create inconsistencies
    // First add lt==0 to the polyhedron and then check consistency
    // create a polyhedron poly with ineqExprs /\ l1 ==0
    C_Polyhedron poly(*ineqExprs);
    Linear_Expression l1 = lt.toLinExpression();
    poly.add_constraint(l1 == 0);
    return checkConsistent(poly);
}

DisequalityStore::~DisequalityStore() {
    delete (disEquals);
}
