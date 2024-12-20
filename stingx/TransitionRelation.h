
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
 * Filename: Location
 * Author: Sriram Sankaranarayanan< srirams@theory.stanford.edu>
 * Comments:
 *    Contains transition relation information. Computes duals, posts, and such
 * things. Post-Comments: SACRED CODE. Reimplemented from scratch for the
 * DUCHESS project. Copyright: see README file for the copyright.
 */

#ifndef __TRANSITION_RELATION__H_
#define __TRANSITION_RELATION__H_

#include <iostream>

#include "Clump.h"
#include "Context.h"
#include "Expression.h"
#include "ExpressionStore.h"
#include "LinTransform.h"
#include "Location.h"
#include "SparseLinExpr.h"
#include "ppl.hh"
#include "var-info.h"

using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;

extern int getLocIndex(string locName);


class TransitionRelation {
   private:
    int varsNum;
    var_info *info, *coefInfo, *lambdaInfo,
        *primedInfo;  // lambdaInfo is the var_info for non-linear multipliers
    Location *preLoc, *postLoc;
    // the actual transition relation as a 2n dimensional polyhedron
    C_Polyhedron* transPoly;

    // structure of the transition relation
    // the structure in rel has been factored into , guard, update and preserved
    // for faster post computation.
    C_Polyhedron *guard, *update;
    set<int> preserved;

    int constraints_num;  // the range multipliers in its coef and the
                                    // number of constraint variables
    int index;  // The index of the non-linear multiplier in lambdaInfo

    string name;
    void initialize(int varsNum,
                    var_info* info,
                    var_info* coefInfo,
                    var_info* lambdaInfo,
                    Location* preLoc,
                    Location* postLoc,
                    C_Polyhedron* rel,
                    string name);
    void initialize(int varsNum,
                    var_info* info,
                    var_info* coefInfo,
                    var_info* lambdaInfo,
                    string name);

    void InitWithoutPopulating(int varsNum,
                                       var_info* info,
                                       var_info* coefInfo,
                                       var_info* lambdaInfo,
                                       Location* preLoc,
                                       Location* postLoc,
                                       C_Polyhedron* rel,
                                       string name,
                                       int index);
    void InitWithoutPopulating(int varsNum,
                                       var_info* info,
                                       var_info* coefInfo,
                                       var_info* lambdaInfo,
                                       string name,
                                       int index);

    bool is_preserved(int i) const;
    bool add_guard(Constraint const& cc);
    bool add_preservation_relation(Constraint const& cc);
    bool split_relation();  // if expression is of the for 'x-x , then add


   public:
    TransitionRelation(int varsNum,
                       var_info* info,
                       var_info* coefInfo,
                       var_info* lambdaInfo,
                       Location* preLoc,
                       Location* postLoc,
                       C_Polyhedron* rel,
                       string name);

    TransitionRelation(int varsNum,
                       var_info* info,
                       var_info* coefInfo,
                       var_info* lambdaInfo,
                       string name);

    TransitionRelation(int varsNum,
                       var_info* info,
                       var_info* coefInfo,
                       var_info* lambdaInfo,
                       Location* preLoc,
                       Location* postLoc,
                       C_Polyhedron* rel,
                       string name,
                       int index);

    TransitionRelation(int varsNum,
                       var_info* info,
                       var_info* coefInfo,
                       var_info* lambdaInfo,
                       string name,
                       int index);

    void setLocs(Location* preLoc, Location* postLoc);
    void setRel(C_Polyhedron* rel);

    void ResetConstraintsNum();

    void strengthen(const C_Polyhedron* p);

    void compute_post(const C_Polyhedron* p, C_Polyhedron& q) const;
    void compute_post_new(const C_Polyhedron* p, C_Polyhedron& q) const;

    void ComputeIntraConsecConstraints(Context& c);

    void ComputeIntraConsecConstraints(vector<Clump>& clumps);

    void ComputeInterConsecConstraints(vector<Clump>& clumps);

    void populateMultipliers();  // Compute the number of multipliers required
                                  // and add them to the constraint store

    int get_mult_index() const { return index; }
    bool matches(string& info) const;
    const string& getName() const;

    const string& getPreLocName() const;
    const int get_preloc_index() const {
        return getLocIndex(getPreLocName());
    }
    const string& getPostLocName() const;
    const int get_postloc_index() const {
        return getLocIndex(getPostLocName());
    }

    // add a pre-assigned invariant (i.e. Location::preInv) that used to
    // strengthen transitions
    void addPreInv();

    const C_Polyhedron& getTransRel() const;
    C_Polyhedron* getTransRelRef() const;
    const var_info* getInfo() const;

    C_Polyhedron const& get_guard_poly() const { return (*guard); }

    C_Polyhedron const& get_update_poly() const { return (*update); }

    set<int> const& get_preserved_set() const { return preserved; }

    void check_map();
};

ostream& operator<<(ostream& in, TransitionRelation const& t);

#endif
