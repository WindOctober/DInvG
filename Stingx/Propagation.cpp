
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

#include "Propagation.h"

#include "Macro.h"

extern int getLocIndex(string locName);
extern vector<int> get_intertid_from_prelid_without_some(int prelid,
                                                         string some);
extern vector<int> get_intertid_to_postlid(int postlid);
extern void collect_invariants_for_one_location_from_intra(vector<Clump>& clumps,
                                                           int loc_index);
extern vector<Location*>* locList;
extern vector<TransitionRelation*>* transList;
extern vector<int>** location_matrix;

void push_back_alltrans_from_location(int loc_index,
                                      vector<int>& trans_bfslist) {
    int loclist_size = locList->size();
    vector<int>::iterator trans_index;
    cout << endl
         << "+ Push back all transitions from location:: "
         << (*locList)[loc_index]->getName();

    cout << endl << "+ " << (*locList)[loc_index]->getName() << ": ";
    for (int j = 0; j < loclist_size; j++) {
        cout << "[";
        for (vector<int>::iterator it = location_matrix[loc_index][j].begin();
             it < location_matrix[loc_index][j].end(); it++) {
            if (j == loc_index) {
                // ignore the intra-transitions which points to themselves
                cout << "-" << *it << "-";
            } else if ((*locList)[j]->get_ppg_flag()) {
                // ignore the transitions which post-location has been
                // propagated
                cout << "-" << *it << "-";
            } else {
                cout << "+" << *it << "+";
                trans_bfslist.push_back(*it);
            }
        }
        cout << "]->" << (*locList)[j]->getName() << ";  ";
    }
    cout << endl << "+ " << trans_bfslist.size() << " transitions [";
    for (vector<int>::iterator i = trans_bfslist.begin();
         i < trans_bfslist.end(); i++) {
        cout << " " << (*i) << " ";
    }
    cout << "] be pushed in bfslist";
}

void push_back_alltrans_from_transition(int propagate_trans_index,
                                        vector<int>& trans_bfslist) {
    string post_location_name =
        (*transList)[propagate_trans_index]->getPostLocName();
    int post_location_index = getLocIndex(post_location_name);
    cout << endl
         << "- Push back all transitions from transition:: "
         << (*transList)[propagate_trans_index]->getName();
    cout << endl << "- Post Location Name: " << post_location_name;
    push_back_alltrans_from_location(post_location_index, trans_bfslist);
}

void propagate_invariants(C_Polyhedron& preloc_inv,
                          C_Polyhedron& trans_relation,
                          int postloc_index) {
    //
    // learn from the following function in Location
    // (*locList)[postloc_index]->propagate_invariants_for_except_initial_by_propagation(preloc_inv,
    // trans_relation);
    //
    Constraint_System cs_preloc_inv = preloc_inv.minimized_constraints();
    C_Polyhedron ph = trans_relation;
    int varsNum = (*locList)[postloc_index]->getDim();
    C_Polyhedron result;

    // following could be replaced by other projection-method or matrix-method
    /*
     * An error log, 2022/10/07
     * ph.intersection_assign(preInv);
     * Aborted: terminate called after throwing an instance
     * of 'std::invalid_argument', what():
     * PPL::C_Polyhedron::intersection_assign(y):
     * this->space_dimension() == 4, y.space_dimension() == 2.
     */
    ph.add_constraints(cs_preloc_inv);
    cout << endl << "* After intersection " << endl << "  " << ph;
    result = swap_index_and_divide_from(ph, varsNum);
    result.remove_higher_space_dimensions(varsNum);
    // finally, record the result
    (*locList)[postloc_index]->invariant_intersected_with(result);
    /*
    // add current invariants to global invariants
    Constraint_System cs_inv = result.minimized_constraints();
    C_Polyhedron poly_inv(result.space_dimension(), UNIVERSE);
    Linear_Expression lin_inv(0);
    */
    cout << endl
         << "* Propagated Invariant at "
         << (*locList)[postloc_index]->getName() << endl
         << "  " << (*locList)[postloc_index]->GetInv();
}

void propagation_invariants(C_Polyhedron& preloc_inv,
                            C_Polyhedron& trans_relation,
                            int postloc_index,
                            C_Polyhedron& p) {
    //
    // learn from the following function in Location
    // (*locList)[postloc_index]->propagate_invariants_for_except_initial_by_propagation(preloc_inv,
    // trans_relation);
    //
    Constraint_System cs_preloc_inv = preloc_inv.minimized_constraints();
    C_Polyhedron ph = trans_relation;
    int varsNum = (*locList)[postloc_index]->getDim();
    C_Polyhedron result;

    // following could be replaced by other projection-method or matrix-method
    /*
     * An error log, 2022/10/07
     * ph.intersection_assign(preInv);
     * Aborted: terminate called after throwing an instance
     * of 'std::invalid_argument', what():
     * PPL::C_Polyhedron::intersection_assign(y):
     * this->space_dimension() == 4, y.space_dimension() == 2.
     */
    ph.add_constraints(cs_preloc_inv);
    cout << endl << "* After intersection " << endl << "  " << ph;
    result = swap_index_and_divide_from(ph, varsNum);
    result.remove_higher_space_dimensions(varsNum);

    cout << endl
         << "* Propagated Invariant at "
         << (*locList)[postloc_index]->getName() << endl
         << "  " << result;

    p = result;
    // return result;
}

void propagate_from_inv_to_initval(C_Polyhedron& preloc_inv,
                                   C_Polyhedron& trans_relation,
                                   int postloc_index) {
    //
    // learn from the following function in Propagation.cc
    // void propagate_invariants(C_Polyhedron & preloc_inv, C_Polyhedron &
    // trans_relation, int postloc_index);
    //
    Constraint_System cs_preloc_inv = preloc_inv.minimized_constraints();
    C_Polyhedron ph = trans_relation;
    int varsNum = (*locList)[postloc_index]->getDim();
    C_Polyhedron result;

    // following could be replaced by other projection-method or matrix-method
    /*
     * An error log, 2022/10/07
     * ph.intersection_assign(preInv);
     * Aborted: terminate called after throwing an instance
     * of 'std::invalid_argument', what():
     * PPL::C_Polyhedron::intersection_assign(y):
     * this->space_dimension() == 4, y.space_dimension() == 2.
     */
    ph.add_constraints(cs_preloc_inv);
    cout << endl << "* After intersection " << endl << "  " << ph;
    result = swap_index_and_divide_from(ph, varsNum);
    result.remove_higher_space_dimensions(varsNum);
    // finally, record the result
    // if (!result.is_empty()){
        (*locList)[postloc_index]->setInitPoly(result);

        cout << endl
         << "* Propagated Initial-value at "
         << (*locList)[postloc_index]->getName() << endl
         << "  " << (*locList)[postloc_index]->getPolyRef();
    // }
}

void propagate_from_inv_to_inv_by_transition(int trans_index) {
    string trans_name = (*transList)[trans_index]->getName();
    string preloc_name = (*transList)[trans_index]->getPreLocName();
    string postloc_name = (*transList)[trans_index]->getPostLocName();
    int preloc_index = getLocIndex(preloc_name);
    int postloc_index = getLocIndex(postloc_name);

    //  prepare the constraints for location invariant and transition relation
    C_Polyhedron preloc_inv = (*locList)[preloc_index]->GetInv();
    C_Polyhedron trans_relation = (*transList)[trans_index]->getTransRel();
    C_Polyhedron postloc_inv = (*locList)[postloc_index]->GetInv();
    cout << endl << "= Location " << postloc_name << " is being Propagated:";
    (*locList)[postloc_index]->ppg_flag_betrue();
    cout << endl
         << "= From Location invariant " << preloc_name << endl
         << "  " << preloc_inv;
    cout << endl
         << "= Through Transition relation " << trans_name << ": " << endl
         << "  " << trans_relation;
    cout << endl
         << "= Propagated Location Invariant " << postloc_name << endl
         << "  " << postloc_inv;

    //  Propagation
    propagate_invariants(preloc_inv, trans_relation, postloc_index);
}

C_Polyhedron propagation_from_inv_to_inv_by_transition(int trans_index) {
    string trans_name = (*transList)[trans_index]->getName();
    string preloc_name = (*transList)[trans_index]->getPreLocName();
    string postloc_name = (*transList)[trans_index]->getPostLocName();
    int preloc_index = getLocIndex(preloc_name);
    int postloc_index = getLocIndex(postloc_name);
    // C_Polyhedron result;

    //  prepare the constraints for location invariant and transition relation
    C_Polyhedron preloc_inv = (*locList)[preloc_index]->GetInv();
    C_Polyhedron trans_relation = (*transList)[trans_index]->getTransRel();
    C_Polyhedron postloc_inv = (*locList)[postloc_index]->GetInv();
    cout << endl << "= Location " << postloc_name << " is being Propagated:";
    //(*locList)[postloc_index]->ppg_flag_betrue();
    cout << endl
         << "= From Location invariant " << preloc_name << endl
         << "  " << preloc_inv;
    cout << endl
         << "= Through Transition relation " << trans_name << ": " << endl
         << "  " << trans_relation;
    cout << endl
         << "= Propagated Location Invariant " << postloc_name << endl
         << "  " << postloc_inv;

    //  Propagation
    Constraint_System cs_preloc_inv = preloc_inv.minimized_constraints();
    C_Polyhedron result = trans_relation;
    int varsNum = (*locList)[postloc_index]->getDim();
    // following could be replaced by other projection-method or matrix-method
    result.add_constraints(cs_preloc_inv);
    cout << endl << "* After intersection " << endl << "  " << result;

    result = swap_index_and_divide_from(result, varsNum);
    result.remove_higher_space_dimensions(varsNum);
    cout << endl
         << "* Propagated Invariant at "
         << (*locList)[postloc_index]->getName() << endl
         << "  " << result;

    return result;
}

void propagate_from_inv_to_initval_by_transition(int trans_index) {
    string trans_name = (*transList)[trans_index]->getName();
    string preloc_name = (*transList)[trans_index]->getPreLocName();
    string postloc_name = (*transList)[trans_index]->getPostLocName();
    int preloc_index = getLocIndex(preloc_name);
    int postloc_index = getLocIndex(postloc_name);

    //  prepare the constraints for location invariant and transition relation
    C_Polyhedron preloc_inv = (*locList)[preloc_index]->GetInv();
    C_Polyhedron trans_relation = (*transList)[trans_index]->getTransRel();
    C_Polyhedron* postloc_initval = (*locList)[postloc_index]->get_initial();
    cout << endl << "= Location " << postloc_name << " is being Propagated:";
    //(*locList)[postloc_index]->ppg_flag_betrue();
    cout << endl
         << "= From Location invariant " << preloc_name << endl
         << "  " << preloc_inv;
    cout << endl
         << "= Through Transition relation " << trans_name << ": " << endl
         << "  " << trans_relation;
    cout << endl
         << "= Propagated Location Initial-value " << postloc_name << endl
         << "  " << *postloc_initval;

    //  Propagation
    propagate_from_inv_to_initval(preloc_inv, trans_relation, postloc_index);
}

void propagate_invariants_from_initial_location_to_all_others() {
    //
    // propagate invariants from initial location
    //
    vector<Location*>::iterator vl;
    vector<int>::iterator trans_index;
    int loclist_size = locList->size();
    int initloc_index;
    cout << endl
         << "> > > propagate_invariants_from_initial_location_to_all_others()";

    // only compute invariants at initial location
    for (int target_index = 0; target_index < loclist_size; target_index++) {
        bool has_initial_poly_set =
            (*locList)[target_index]->getInitFlag();
        if (!has_initial_poly_set) {
            cout << endl
                 << "- NO. No initial condition in Location::"
                 << (*locList)[target_index]->getName();
        } else {
            initloc_index = target_index;
            cout << endl
                 << "- YES! Initial Location:: "
                 << (*locList)[target_index]->getName();
        }
    }
    // mark "have invariants or not"-flag at each location
    int propagation_flag[loclist_size] = {0};
    propagation_flag[initloc_index] = 1;

    // push back the first set of transitions (from initial location) into
    // bfslist
    vector<int> trans_bfslist;
    cout << endl << "/------------------------------";
    push_back_alltrans_from_location(initloc_index, trans_bfslist);
    (*locList)[initloc_index]->ppg_flag_betrue();
    cout << endl << "\\------------------------------";
    while (!trans_bfslist.empty()) {
        cout << endl << "/------------------------------";
        // pop the front element (the p-transition) in the queue
        int propagate_trans_index = trans_bfslist.front();
        trans_bfslist.erase(trans_bfslist.begin());
        cout << endl
             << "' Prepare the front element, the propagation trans_index: "
             << propagate_trans_index;
        cout << endl << "' " << trans_bfslist.size() << " transitions [";
        for (vector<int>::iterator i = trans_bfslist.begin();
             i < trans_bfslist.end(); i++) {
            cout << " " << (*i) << " ";
        }
        cout << "] remained in bfslist";

        // propagate the p-transition obtained from the front element
        propagate_from_inv_to_inv_by_transition(propagate_trans_index);

        // push back all the transitions (from the post-location of
        // p-transition) into bfslist
        push_back_alltrans_from_transition(propagate_trans_index,
                                           trans_bfslist);
        cout << endl << "\\------------------------------";
    }

    cout << endl
         << "< < < propagate_invariants_from_initial_location_to_all_others()";
    return;
}

vector<int> get_initial_lid() {
    // initialize
    int loclist_size = locList->size();
    vector<int> initial_lid;

    for (int id = 0;
         id < loclist_size && (*locList)[id]->getName() != EXIT_LOCATION;
         id++) {
        bool isInitLoc = (*locList)[id]->isInitLoc();
        if (!isInitLoc) {
            cout << endl
                 << "- NO. No initial condition in Location::"
                 << (*locList)[id]->getName();
        } else {
            initial_lid.push_back(id);
            cout << endl
                 << "- YES! Initial Location:: " << (*locList)[id]->getName();
        }
    }

    return initial_lid;
}

vector<int> get_exit_vlid() {
    // initialize
    vector<int> exit_lid;

    exit_lid.push_back(getLocIndex(EXIT_LOCATION));

    return exit_lid;
}

int get_exit_lid() {
    // initialize
    int exit_lid;

    exit_lid = getLocIndex(EXIT_LOCATION);

    return exit_lid;
}

bool has_empty_ppg_flag_except_exit() {
    // initialize before propagation
    int loclist_size = locList->size();
    bool all_ppg_flag = true;

    for (int id = 0;
         id < loclist_size && (*locList)[id]->getName() != EXIT_LOCATION;
         id++) {
        all_ppg_flag &= (*locList)[id]->get_ppg_flag();
    }
    cout << endl << "* all_ppg_flag: " << all_ppg_flag;

    return !all_ppg_flag;
}

bool invgen_need_working() {
    cout << endl;
    cout << endl << "> > > invgen_need_working()";
    // if all ppg_flag (except exit) is true, invgen is over
    if (!has_empty_ppg_flag_except_exit()) {
        cout << endl << "! invgen is over !";
        cout << endl << "< < < invgen_need_working()";
        return false;
    }

    // if ppging_lid.size() == 0, invgen is over
    vector<int>::iterator it;
    vector<int> ppging_lid = get_ppging_lid();
    cout << endl << "' " << ppging_lid.size() << " location [";
    for (it = ppging_lid.begin(); it < ppging_lid.end(); it++) {
        cout << " " << (*it) << " ";
    }
    cout << "] remained in ppging_lid";
    if (ppging_lid.size() == 0) {
        cout << endl << "! invgen is over !";
        cout << endl << "< < < invgen_need_working()";
        return false;
    }

    cout << endl << "< < < invgen_need_working()";
    return true;
}

vector<int> get_ppging_lid() {
    vector<int> ppging_lid;
    int loclist_size = locList->size();

    for (int id = 0;
         id < loclist_size && (*locList)[id]->getName() != EXIT_LOCATION;
         id++) {
        if ((*locList)[id]->get_ppging_flag()) {
            ppging_lid.push_back(id);
        }
    }

    return ppging_lid;
}

vector<int> get_ppging_tid(vector<int> ppging_lid) {
    vector<int> ppging_tid;
    vector<int>::iterator it;

    for (it = ppging_lid.begin(); it < ppging_lid.end(); it++) {
        vector<int> tid =
            get_intertid_from_prelid_without_some(*it, EXIT_LOCATION);
        ppging_tid.insert(ppging_tid.end(), tid.begin(), tid.end());
    }

    return ppging_tid;
}

vector<int> get_ppged_lid() {
    vector<int> ppged_lid;
    int loclist_size = locList->size();

    for (int id = 0;
         id < loclist_size && (*locList)[id]->getName() != EXIT_LOCATION;
         id++) {
        if ((*locList)[id]->get_ppged_flag()) {
            ppged_lid.push_back(id);
        }
    }

    return ppged_lid;
}

vector<int> get_exitic_tid(int exit_lid) {
    vector<int> exitic_tid;
    vector<int>::iterator it;

    exitic_tid = get_intertid_to_postlid(exit_lid);
    for (it = exitic_tid.begin(); it < exitic_tid.end(); it++) {
        int pre_lid = (*transList)[*it]->get_preloc_index();
        if (!(*locList)[pre_lid]->get_ppg_flag()) {
            cout << endl
                 << "id: " << pre_lid << ", Location "
                 << (*locList)[pre_lid]->getName()
                 << ", ppg_flag is false, erase one of the exitic_tid";
            it = exitic_tid.erase(it);
            it--;
        }
    }

    return exitic_tid;
}

void InvPropagation(vector<Clump>& clumps) {
    // initialize before propagation
    int loclist_size = locList->size();
    vector<int>::iterator it;
    cout << endl;
    cout << endl << "> > > InvPropagation()";

    /*
     * First, compute other location except Initial & Exit-Location
     */
    // (1) propagation from initial-locations with initial-value (should have
    // computed invariants)
    vector<int> initial_lid = get_initial_lid();
    cout << endl << "' " << initial_lid.size() << " location [";
    for (it = initial_lid.begin(); it < initial_lid.end(); it++) {
        cout << " " << (*it) << " ";
        (*locList)[*it]->ppging_flag_betrue();
        (*locList)[*it]->ppg_flag_betrue();
    }
    cout << "] remained in initial_lid";

    // (2) compute initial-value by propagation and compute invariants by farkas
    while (invgen_need_working()) {
        cout << endl
             << "/------------------------------(Propagation with Farkas)";
        // 1 propagation
        vector<int> ppging_lid = get_ppging_lid();
        cout << endl << "' Propagation";
        cout << endl << "' " << ppging_lid.size() << " location [";
        for (it = ppging_lid.begin(); it < ppging_lid.end(); it++) {
            cout << " " << (*it) << " ";
        }
        cout << "] remained in ppging_lid";
        vector<int> ppging_tid = get_ppging_tid(ppging_lid);
        cout << endl << "' " << ppging_tid.size() << " transition [";
        for (it = ppging_tid.begin(); it < ppging_tid.end(); it++) {
            cout << " " << (*it) << " ";
        }
        cout << "] remained in ppging_tid";
        for (it = ppging_tid.begin(); it < ppging_tid.end(); it++) {
            // 1.1 PROPAGATION compute initial-value
            propagate_from_inv_to_initval_by_transition(*it);
            // 1.2 TURN-ON ppged-flag
            int post_lid = (*transList)[*it]->get_postloc_index();
            (*locList)[post_lid]->ppged_flag_betrue();
        }
        // 1.3 TURN-OFF all ppging_flag, which means propagation over
        for (it = ppging_lid.begin(); it < ppging_lid.end(); it++) {
            (*locList)[*it]->ppging_flag_befalse();
        }

        // 2 farkas
        vector<int> ppged_lid = get_ppged_lid();
        cout << endl << "' Farkas";
        cout << endl << "' " << ppged_lid.size() << " location [";
        for (it = ppged_lid.begin(); it < ppged_lid.end(); it++) {
            cout << " " << (*it) << " ";
        }
        cout << "] remained in ppged_lid";
        if (ppged_lid.size() == 1) {
            int lid = ppged_lid[0];
            // 2.1 FARKAS compute invariant
            collect_invariants_for_one_location_from_intra(clumps, lid);
            // 2.2 TURN-ON ppging-flag
            (*locList)[lid]->ppging_flag_betrue();
            // 2.3 TURN-ON ppg-flag
            (*locList)[lid]->ppg_flag_betrue();
        } else {
            cout << endl
                 << "Warning: there are " << ppged_lid.size()
                 << " location need to be computed invariants by Farkas";
        }
        // 2.4 TURN-OFF all ppged_flag, which means Farkas over
        for (it = ppged_lid.begin(); it < ppged_lid.end(); it++) {
            (*locList)[*it]->ppged_flag_befalse();
        }
        cout << endl
             << "\\------------------------------(Propagation with Farkas)";
    }

    /*
     * Second, compute Exit-Location only by propagation
     */
    int exit_lid = get_exit_lid();
    vector<int> exitic_tid;

    exitic_tid = get_exitic_tid(exit_lid);
    for (it = exitic_tid.begin(); it < exitic_tid.end(); it++) {
        cout << endl
             << "/------------------------------(Propagation to Exit-Location)";
        C_Polyhedron one_djinv_clause =
            propagation_from_inv_to_inv_by_transition(*it);
        (*locList)[exit_lid]->set_vp_inv(one_djinv_clause);
        cout
            << endl
            << "\\------------------------------(Propagation to Exit-Location)";
    }

    cout << endl << "< < < InvPropagation()";
    return;
}
