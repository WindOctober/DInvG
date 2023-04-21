
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
#include "DualInvariantMap.h"
#include "DualTransitionRelation.h"
#include "Expression.h"
#include "ExpressionStore.h"
#include "InvariantMap.h"
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
    //  f_, fd_, fr_ // the var-infos

    var_info *f_, *fd_, *fr_;

    int n_, nd_, r_;

    long int propagation_time, widening_time;

    Context *glc_;
    // one for each location
    vector<Location *> vloc;

    vector<TransitionRelation *> vtrans;

    vector<DualTransitionRelation> vdtrans;

    void compute_initial_context();
    bool context_computed_;

    void get_location_info(System &s, Context &cc);

    void get_transition_info(System &s, Context &cc);

    void do_some_propagation(InvariantMap &im);

    void dual_propagation(DualInvariantMap &dim);

   public:
    System(var_info *f_, var_info *fd_, var_info *fr_);

    System(System &s, Context &cc);

    void add_location(Location *loc);
    void add_transition(TransitionRelation *trans);

    void compute_duals();

    // the inlines

    int num_loc() const { return vloc.size(); }

    int num_trans() const { return vtrans.size(); }

    var_info *get_var_info() const { return f_; }

    var_info *get_dual_var_info() const { return fd_; }

    var_info *get_multiplier_var_info() const { return fr_; }

    int get_n() const { return n_; }
    int get_nd() const { return nd_; }

    int get_r() const { return r_; }

    // the non-inlines
    void
    update_dimensions();  // recompute the r_ and nd_ based on the information
    // void populate_multipliers();

    Location const &get_location(int i) const;

    Location *get_matching_location(string name);
    bool location_matches(string name);

    TransitionRelation const &get_transition_relation(int i) const;

    void print(ostream &os) const;

    Context *get_context();

    void add_invariants_and_update(C_Polyhedron &pp, C_Polyhedron &dualp);

    void obtain_trivial_polyhedron(C_Polyhedron &invd);

    // compute bhrz03 and h79 invariants!

    void compute_invariant(InvariantMap &im);
    void compute_invariant_h79(InvariantMap &im);

    void compute_dual_invariant(InvariantMap &im);
};

ostream &operator<<(ostream &out, System const &sys);

#endif
