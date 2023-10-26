
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
 * Filename: System
 * Author: Sriram Sankaranarayanan< srirams@theory.stanford.edu>
 * Comments: A transition system implementation. skeleton for very naive
 *           iteration implemented. CH79 and BHrz03 invariants are computed from
 * here. Copyright: see README file for this information.
 */

#ifndef D__SYSTEM__H_
#define D__SYSTEM__H_

#include <iostream>
#include <vector>

#include "Clump.h"
#include "Context.h"
#include "Expression.h"
#include "ExpressionStore.h"
#include "LinTransform.h"
#include "Location.h"
#include "Timer.h"
#include "TransitionRelation.h"
#include "ppl.hh"
#include "var-info.h"

using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;

class System {
    //
    // just a collection of locations and transition systems
    // this facilitates running algorithms on it
    // rather than the messy thing in the .y file
    //

   private:
    // members are
    //  varInfo, coefInfo, lambdaInfo // the var-infos

    var_info *varInfo, *coefInfo, *lambdaInfo;
    int varNum, coefNum, lamdaNum;
    long int propagation_time, widening_time;

    Context* glc_;
    // one for each location
    vector<Location*> vecLocs;

    vector<TransitionRelation*> vecTrans;


    void compute_initial_context();
    bool context_computed_;

    void get_location_info(System& s, Context& cc);

    void get_transition_info(System& s, Context& cc);


   public:
    System(var_info* varInfo, var_info* coefInfo, var_info* lambdaInfo);
    System(System& s, Context& cc);

    void addLoc(Location* loc);
    void addTrans(TransitionRelation* trans);

    int getLocNum() const { return vecLocs.size(); }
    int getTransNum() const { return vecTrans.size(); }

    var_info* getInfo() const { return varInfo; }
    var_info* getCoefInfo() const { return coefInfo; }
    var_info* getLambdaInfo() const { return lambdaInfo; }
    int getVarNum() const { return varNum; }
    int getCoefNum() const { return coefNum; }
    int getLambdaNum() const { return lamdaNum; }

    // the non-inlines
    void update_dimensions();  // recompute the lamdaNum and coefNum based on the information
    // void populate_multipliers();

    Location const& get_location(int i) const;

    Location* get_matching_location(string name);
    bool location_matches(string name);

    TransitionRelation const& get_transition_relation(int i) const;

    void print(ostream& os) const;
    Context* getContext();

    void add_invariants_and_update(C_Polyhedron& pp, C_Polyhedron& dualp);

};

ostream& operator<<(ostream& out, System const& sys);

#endif
