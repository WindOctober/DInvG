
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
 * Filename: Propagation.cc
 * Author: Hongming Liu<hm-liu@sjtu.edu.cn>
 * Comments: Some Propagation methods for collecting invariants.
 * Copyright: Please see README file.
 */

#ifndef __PROPAGATION__H_
#define __PROPAGATION__H_

#include <iostream>
#include <queue>

#include "Elimination.h"
#include "Location.h"
#include "TransitionRelation.h"
#include "ppl.hh"

using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;

// push back all the transitions (from location) into bfslist
void push_back_alltrans_from_location(int loc_index,
                                      vector<int>& trans_bfslist);

// push back all the transitions (from the post-location of p-transition) into
// bfslist
void push_back_alltrans_from_transition(int propagate_trans_index,
                                        vector<int>& trans_bfslist);

// propagate invariants from preloc into postloc by projection or matrix-method
void propagate_invariants(C_Polyhedron& preloc_inv,
                          C_Polyhedron& trans_relation, int postloc_index);

// propagate invariants from preloc into postloc by projection or matrix-method
// return the C_Polyhedron::propagation-result
void propagation_invariants(C_Polyhedron& preloc_inv,
                            C_Polyhedron& trans_relation, int postloc_index,
                            C_Polyhedron& p);

// propagate the preloc's invariants into postloc's initial-value by projection
// or matrix-method
void propagate_from_inv_to_initval(C_Polyhedron& preloc_inv,
                                   C_Polyhedron& trans_relation,
                                   int postloc_index);

// propagate the p-transition obtained from the front element, from pre's
// invariant to post's invariant
void propagate_from_inv_to_inv_by_transition(int trans_index);

// propagate the p-transition obtained from the front element, from pre's
// invariant to post's invariant return the C_Polyhedron::propagation-result
C_Polyhedron propagation_from_inv_to_inv_by_transition(int trans_index);

// propagate the p-transition, which is obtained from the front element, from
// pre's invariants to post's initial-value
void propagate_from_inv_to_initval_by_transition(int trans_index);

// propagate invariants from initial location
void propagate_invariants_from_initial_location_to_all_others();

// return the initial-location-index which has initial-value and should have
// computed invariants
vector<int> get_initial_lid();

// return the vector of exit-location-index
vector<int> get_exit_vlid();

// return the exit-location-index
int get_exit_lid();

// has locations which has not been computed invariants by propagation
bool has_empty_ppg_flag_except_exit();

// all invariants are worked out, which means that there is no empty ppg_flag or
// there is no location need to compute propagation and Farkas
bool invgen_need_working();

// return the location-index which will propagate to others
vector<int> get_ppging_lid();

// return the transition-index which will propagate to others
vector<int> get_ppging_tid();

// return the location-index which has initial-value, ppged_flag and should be
// computed invariants by farkas
vector<int> get_ppged_lid();

// return the transition-index which postloc is exit-loction
// exit-incoming, i.e. towards to exit
vector<int> get_exitic_tid();

// compute other invariants by propagation with Farkas
void compute_invariants_by_propagation_with_farkas(vector<Clump>& vcl);

#endif