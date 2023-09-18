
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
 * A location contains information about a location.
 * Information includes outgoing transitions
 * The location specific coef variables are all kept in
 * a var-info created for that purpose
 * a range of indices [l,r) is specified over that locations specific
 * variables
 * Post-Comments: SACRED CODE. Reimplemented for the DUCHESS project.
 * Copyright: see README file for the copyright.
 */

#ifndef __LOCATION__H_
#define __LOCATION__H_

#include <iostream>
#include <string>

#include "Clump.h"
#include "Context.h"
#include "ppl.hh"
#include "var-info.h"

using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;

class Location {
   private:
    int varsNum;                  // the number of variables in the location
    var_info *info, *coefInfo, *lambdaInfo;  // the primal and coef var-infos
    bool initFlag=false;           // has the initial condition been set
    string loc_name;            // name
    Context* context;             // the solver for intra-location transitions
    C_Polyhedron* poly;        // the initial condition
    // If there is none, then initialized to false

    // the final invariant that I will compute for the location
    // Post-comments: To do.. change this into an invariant map. I did this
    // initially so that I could run auto-strengthening. But this is to
    // cumbersome.
    C_Polyhedron* invariant;

    // the final invariant that will be computed for the location
    // which is a disjunctive form stored in a vector.
    Clump vp_inv;

    // location has a disjunctive-form invariant
    bool vp_inv_flag;

    // A pre-assigned invariant that i will use to strengthen transitions.
    C_Polyhedron* loc_inv;

    // A vector of polyhedra stores the disabled-path condition
    Clump* disabled_clump;

    // has context been made
    bool contextReady;

    // the left-most index of the coefficient variable.. the coefficients for
    // the parametric invariants for the location span the range [l.. l+varsNum]
    int LIndex;

    // Initialize and form parametric coefficients for the invariant
    void initialize(int varsNum,
                    var_info* info,
                    var_info* coefInfo,
                    var_info* lambdaInfo,
                    C_Polyhedron* p,
                    string name);
    // Initialize but do not form new coefficients
    void InitWithoutPopulating(int varsNum,
                                       var_info* info,
                                       var_info* coefInfo,
                                       var_info* lambdaInfo,
                                       C_Polyhedron* p,
                                       string name,
                                       int left);

    // added by Hongming, 2022/10/11, Shanghai Jiao Tong University

    // Record whether this location has been propagated in bfslist
    bool propagation_flag;
    // record whether this location has propagating to others
    bool ppging_flag;
    // record whether this location has been propagated by others
    bool ppged_flag;

   public:
    Location(int varsNum,
             var_info* info,
             var_info* coefInfo,
             var_info* lambdaInfo,
             C_Polyhedron* p,
             string name);

    Location(int varsNum, var_info* info, var_info* coefInfo, var_info* lambdaInfo, string name);

    // A location with preset var-infos and a given starting point

    Location(int varsNum,
             var_info* info,
             var_info* coefInfo,
             var_info* lambdaInfo,
             string name,
             int left);

    Location(int varsNum,
             var_info* info,
             var_info* coefInfo,
             var_info* lambdaInfo,
             C_Polyhedron* p,
             string name,
             int left);

    // set the initial polyhedron from q into p
    void setPoly(C_Polyhedron* q);
    // set the initial-value polyhedron from q to this
    void setInitPoly(C_Polyhedron& q);
    bool has_initial();

    void addClump(vector<Clump>& clumps);
    void make_context();

    void ComputeDualConstraints();
    void ComputeDualConstraints(Context& cc);       // the coef constraints
    void ComputeDualConstraints(C_Polyhedron& cc);  // the coef constraints

    int getDim() const;
    const var_info* getInfo() const;
    const var_info* getCoefInfo() const;
    int getLIndex() const;

    bool matches(string name) const;

    C_Polyhedron const& getPolyRef() const {
        if (initFlag)
            return (*poly);
        cerr << " asked reference when poly is not set " << endl;
        abort();
    }

    C_Polyhedron& invariant_reference() { return (*invariant); }
    C_Polyhedron const& GetInv() const { return *invariant; }
    void invariant_intersected_with(C_Polyhedron& what) {
        invariant->intersection_assign(what);
    }

    // push back disjunctive-invariant into vector-poly
    void set_vp_inv(C_Polyhedron& what) {
        vp_inv.insert(what);
        vp_inv_flag = true;
    }
    void set_vp_inv(C_Polyhedron* what) {
        vp_inv.insert(*what);
        vp_inv_flag = true;
    }
    bool get_vp_inv_flag() const { return vp_inv_flag; }

    Clump const& get_vp_inv() const { return vp_inv; }

    C_Polyhedron* get_initial();

    Context* get_context();

    bool getInitFlag() const { return initFlag; }

    void force_polyset() {
        cerr << " Encountered a call to Location::force_poly_set()" << endl;
        abort();
        initFlag = true;
    }

    C_Polyhedron& get_non_const_poly_reference() { return *poly; }

    void set_invariant_polyhedron(C_Polyhedron* what) {
        loc_inv->intersection_assign((*what));
    }

    C_Polyhedron const& inv_poly_reference() const { return (*loc_inv); }

    Clump* getDisClump() { return disabled_clump; }
    Clump const& getDisClumpRef() const { return (*disabled_clump); }

    // return the propagation_flag, which records whether this location has been
    // propagated in bfslist
    bool get_ppg_flag() const { return propagation_flag; }
    // set the propagation_flag to be true, which records whether this location
    // has been propagated in bfslist
    void ppg_flag_betrue() { propagation_flag = true; }
    // set the propagation_flag to be false, which records whether this location
    // has been propagated in bfslist
    void ppg_flag_befalse() { propagation_flag = false; }

    // return ppging_flag, which records whether this location has propagating
    // to others
    bool get_ppging_flag() const { return ppging_flag; }
    // set ppging_flag to be true, which records whether this location has
    // propagating to others
    void ppging_flag_betrue() { ppging_flag = true; }
    // set ppging_flag to be false, which records whether this location has
    // propagating to others
    void ppging_flag_befalse() { ppging_flag = false; }
    // return ppged_flag, which records whether this location has been
    // propagated by others
    bool get_ppged_flag() const { return ppged_flag; }
    // set ppged_flag to be true, which records whether this location has been
    // propagated by others
    void ppged_flag_betrue() { ppged_flag = true; }
    // set ppged_flag to be false, which records whether this location has been
    // propagated by others
    void ppged_flag_befalse() { ppged_flag = false; }

    void extract_invariants_and_update(C_Polyhedron& pp, C_Polyhedron& dualp);
    void extract_invariants_and_update_for_one_location_by_eliminating(
        C_Polyhedron& pp,
        C_Polyhedron& dualp);
    void propagate_invariants_and_update_for_except_initial_by_propagation(
        C_Polyhedron& preloc_inv,
        C_Polyhedron& trans_rel /*, C_Polyhedron & dualp*/);
    void contains_test(C_Polyhedron& pp,
                       C_Polyhedron& loc_inv,
                       C_Polyhedron& trans_rel);
    void extract_invariants_and_update_for_initial_by_recursive_eliminating(
        C_Polyhedron& pp,
        C_Polyhedron& dualp);
    void extract_invariants_and_update_by_binary_eliminating(
        C_Polyhedron& pp,
        C_Polyhedron& dualp);

    string const& getName() const;

    void populate_coefficients();  // compute the coefficients required and add
                                   // them to the constraint store
    void add_to_trivial(C_Polyhedron* trivial);
    void add_to_trivial(C_Polyhedron& trivial);

    void initialize_invariant();
    void extract_invariant_from_generator(Generator_System const& g);
    void extract_invariant_from_generator(Generator const& g);
    void extract_invariant_for_one_location_by_eliminating(
        Constraint_System const& c);
    void propagate_invariants_for_except_initial_by_propagation(
        C_Polyhedron& preloc_inv,
        C_Polyhedron& trans_rel);
    void extract_invariant_for_initial_by_recursive_eliminating(
        Constraint_System const& c);
    void solve_invariant_from_generator(Generator_System const& g);
    void solve_invariant_from_generator(Generator const& g);
    void update_dual_constraints(C_Polyhedron& dualp);
};

ostream& operator<<(ostream& in, Location const& l);  // print the location

#endif
