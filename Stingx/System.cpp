
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

#include "System.h"

#include "myassertions.h"

System::System(var_info* info, var_info* coefInfo, var_info* lambdaInfo)
    : varInfo(info),
      coefInfo(coefInfo),
      lambdaInfo(lambdaInfo),
      varNum(info->getDim()),
      coefNum(coefInfo->getDim()),
      lamdaNum(lambdaInfo->getDim()),
      context_computed_(false) {}

System::System(System& s, Context& cc)
    : varInfo(s.getInfo()),
      coefInfo(s.getCoefInfo()),
      lambdaInfo(s.getLambdaInfo()),
      varNum(varInfo->getDim()),
      coefNum(coefInfo->getDim()),
      lamdaNum(lambdaInfo->getDim()),
      context_computed_(false) {
    // now obtain location information from context
    get_location_info(s, cc);
    get_transition_info(s, cc);
}

void System::addLoc(Location* loc) {
    vloc.push_back(loc);
}

void System::addTrans(TransitionRelation* trans) {
    vtrans.push_back(trans);
}

void System::update_dimensions() {
    varNum = varInfo->getDim();
    coefNum = coefInfo->getDim();
    lamdaNum = lambdaInfo->getDim();
}

Location const& System::get_location(int index) const {
    PRECONDITION((index >= 0 && index < getLocNum()),
                 "System::get_location-- index out of range");
    Location const* ll = vloc[index];
    return (*ll);
}

TransitionRelation const& System::get_transition_relation(int index) const {
    PRECONDITION((index >= 0 && index < getTransNum()),
                 "System::get_transition_relation -- index out of range");
    TransitionRelation const* tt = vtrans[index];
    return (*tt);
}


void System::print(ostream& os) const {
    vector<Location*>::const_iterator vi;
    vector<TransitionRelation*>::const_iterator vj;

    os << "System::" << endl;
    os << " =======================================================" << endl;
    os << " System Locations" << endl;

    for (vi = vloc.begin(); vi < vloc.end(); ++vi) {
        os << *(*vi) << endl;
    }

    os << "System Transitions " << endl;

    for (vj = vtrans.begin(); vj < vtrans.end(); ++vj) {
        os << *(*vj) << endl;
    }
}

ostream& operator<<(ostream& os, System const& sys) {
    sys.print(os);
    return os;
}

void System::compute_initial_context() {
    if (context_computed_)
        delete (glc_);

    glc_ = new Context(varInfo, coefInfo, lambdaInfo);

    vector<Location*>::iterator vi;
    for (vi = vloc.begin(); vi != vloc.end(); ++vi) {
        (*vi)->ComputeDualConstraints(*glc_);
    }

    vector<TransitionRelation*>::iterator vj;
    for (vj = vtrans.begin(); vj != vtrans.end(); ++vj) {
        (*vj)->ComputeIntraConsecConstraints(*glc_);
    }
}

Context* System::getContext() {
    if (!context_computed_)
        compute_initial_context();

    return glc_;
}

void System::get_location_info(System& s, Context& cc) {
    int nl = s.getLocNum();
    int i, j;
    for (i = 0; i < nl; ++i) {
        // obtain a new location
        Location const& lc = s.get_location(i);
        j = lc.getLIndex();
        Location* newl = new Location(varNum, varInfo, coefInfo, lambdaInfo, lc.getName(), j);

        newl->force_polyset();
        C_Polyhedron& res = newl->get_non_const_poly_reference();

        cc.obtain_primal_polyhedron(j, res);
        addLoc(newl);
    }

    // that should do it
}

bool System::location_matches(string name) {
    vector<Location*>::iterator vi;
    for (vi = vloc.begin(); vi != vloc.end(); ++vi) {
        if ((*vi)->matches(name))
            return true;
    }
    return false;
}

Location* System::get_matching_location(string name) {
    vector<Location*>::iterator vi;
    for (vi = vloc.begin(); vi != vloc.end(); ++vi) {
        if ((*vi)->matches(name))
            return (*vi);
    }

    INVARIANT(false, "location not matched.. error.. ");

    return (Location*)0;
}

void System::get_transition_info(System& s, Context& cc) {
    int nt = s.getTransNum();
    int i, j, l;

    Location *preLoc, *postLoc;
    C_Polyhedron* res;
    for (i = 0; i < nt; ++i) {
        TransitionRelation const& tc = s.get_transition_relation(i);
        j = tc.get_mult_index();
        string pre = tc.getPreLocName();
        string post = tc.getPostLocName();
        TransitionRelation* newt;
        // 1. obtain matching location.. they better be there
        // 2. compute and set the relation

        if (pre != post) {
            preLoc = get_matching_location(pre);
            postLoc = get_matching_location(post);

            res = new C_Polyhedron(tc.getTransRel());

            newt = new TransitionRelation(varNum, varInfo, coefInfo, lambdaInfo, preLoc, postLoc,
                                          res, tc.getName(), j);
            addTrans(newt);
            continue;
        } else if (pre == post) {
            preLoc = get_matching_location(pre);
            l = preLoc->getLIndex();
            res = new C_Polyhedron(2 * varNum);

            if (cc.obtain_transition_relation(j, l, *res) == false) {
                delete (res);
                delete (newt);
                continue;
            }
            newt = new TransitionRelation(varNum, varInfo, coefInfo, lambdaInfo, preLoc, preLoc, res,
                                          tc.getName(), j);
            addTrans(newt);
        }
    }
}

void System::add_invariants_and_update(C_Polyhedron& pp, C_Polyhedron& dualp) {
    vector<Location*>::iterator vi;
    for (vi = vloc.begin(); vi != vloc.end(); ++vi) {
        (*vi)->extract_invariants_and_update(pp, dualp);
    }

    return;
}