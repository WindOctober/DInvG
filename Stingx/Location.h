
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
    int varsNum;  // the number of variables in the location
    var_info *info, *coefInfo, *lambdaInfo;  // the primal and coef var-infos
    bool initFlag = false;  // has the initial condition been set
    string locName;         // name
    Context* context;       // the solver for intra-location transitions
    C_Polyhedron* poly;     // the initial condition
    // If there is none, then initialized to false

    // the final invariant that I will compute for the location
    // Post-comments: To do.. change this into an invariant map. I did this
    // initially so that I could run auto-strengthening. But this is to
    // cumbersome.
    C_Polyhedron* invariant;
    vector<C_Polyhedron*> assertions;
    // A pre-assigned invariant that i will use to strengthen transitions.
    C_Polyhedron* preInv;

    // A vector of polyhedra stores the disabled-path condition
    Clump* disableClump;

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

   public:
    Location(int varsNum,
             var_info* info,
             var_info* coefInfo,
             var_info* lambdaInfo,
             C_Polyhedron* p,
             string name);

    Location(int varsNum,
             var_info* info,
             var_info* coefInfo,
             var_info* lambdaInfo,
             string name);

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
    bool isInitLoc();

    void addClump(vector<Clump>& clumps);
    void makeContext();

    void ComputeCoefConstraints();
    void ComputeCoefConstraints(Context& cc);       // the coef constraints
    void ComputeCoefConstraints(C_Polyhedron& cc);  // the coef constraints

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

    C_Polyhedron& getInvRef() { return (*invariant); }
    C_Polyhedron const& GetInv() const { return *invariant; }
    void invariant_intersected_with(C_Polyhedron& what) {
        invariant->intersection_assign(what);
    }
    C_Polyhedron* get_initial();

    Context* getContext();

    bool getInitFlag() const { return initFlag; }

    void force_polyset() {
        cerr << " Encountered a call to Location::force_poly_set()" << endl;
        abort();
        initFlag = true;
    }

    C_Polyhedron& get_non_const_poly_reference() { return *poly; }

    void setPreInvPoly(C_Polyhedron* what) {
        preInv->intersection_assign((*what));
        return;
    }
    void setAssertion(vector<C_Polyhedron*> polys) {
        assertions = polys;
        return;
    }

    C_Polyhedron const& getPreInvRef() const { return (*preInv); }

    Clump* getDisClump() { return disableClump; }
    Clump const& getDisClumpRef() const { return (*disableClump); }

    void ExtractAndUpdateInvOrigin(C_Polyhedron& pp, C_Polyhedron& dualp);
    void ExtractAndUpdateInv(C_Polyhedron& pp, C_Polyhedron& dualp);
    void contains_test(C_Polyhedron& pp,
                       C_Polyhedron& preInv,
                       C_Polyhedron& trans_rel);

    string const& getName() const;

    void setCoefInfo();  // compute the coefficients required and add
                         // them to the constraint store
    void addTrivial(C_Polyhedron* trivial);
    void addTrivial(C_Polyhedron& trivial);

    void initInv();
    void ExtractInvfromGenerator(Generator_System const& g);
    void ExtractInvfromGenerator(Generator const& g);
    void ExtractInv(Constraint_System const& c);
    void computeInvFromGenerator(Generator_System const& g);
    void computeInvFromGenerator(Generator const& g);
    void UpdateCoefCS(C_Polyhedron& dualp);
};

ostream& operator<<(ostream& in, Location const& l);  // print the location

#endif
