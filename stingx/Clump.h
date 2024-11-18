
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
 * Filename: Clump.cc
 * Author: Sriram Sankaranarayanan<srirams@theory.stanford.edu>
 * Comments: Clump module holds a disjunction of polyhedral constraints.
 * Copyright: Please see README file.
 */

#ifndef __CLUMP__H_
#define __CLUMP__H_

#include <var-info.h>

#include <iostream>
#include <vector>

#include "ppl.hh"

using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;

class Clump {
   private:
    /*
     * coefNum = num of coef dimensions (depends on what mode the
     *                              analyzer is operated in )
     * coefInfo = var_info for coef -- standard pointer for printing purposes
     *                            that should not be touched
     * vecPolys = vector of polyhedra
     *
     * iter = a pointer to some position in polys.. some sort of a poor
     *        man's iterator. In a future version, this will be made into a
     *        full fledged iterator. Do not see the need for that now.
     *
     */

    int coefNum;
    var_info* coefInfo;
    vector<C_Polyhedron> vecPolys;
    int iter;

    string name;
    string category;

    void initialize();
    void initialize(var_info* coefInfo);
    void initialize(var_info* coefInfo, string name, string category);

   public:
    int getIter();
    int size();
    int space_dimension() const { return vecPolys[0].space_dimension(); }

    const string& getName() const;
    const string& getCategory() const;
    const vector<C_Polyhedron>& getPolysVec() const;
    void replace_vp(vector<C_Polyhedron> new_vp);

    Clump();
    Clump(var_info* coefInfo);
    Clump(var_info* coefInfo, string name, string category);

    int getCount();

    // Insert a polyhedron
    void insert(C_Polyhedron const& p);

    vector<int> insert_with_erase_index(C_Polyhedron const& p);

    vector<int> prune_all(C_Polyhedron& dualp);
    vector<int> prune_target(C_Polyhedron& dualp, int target_gli);

    // Is there a disjunct that contains "what"
    bool contains(C_Polyhedron& what);

    // operations on iter -- the java style is just co-incidental. ;-)
    // self-explanatory :-)

    void resetIter();

    bool has_next();

    C_Polyhedron& getReference();
    C_Polyhedron& getReference(int index);

    void next();
};

inline int Clump::getIter() {
    return iter;
}
inline int Clump::size() {
    return vecPolys.size();
}

inline const string& Clump::getName() const {
    return name;
}

inline const string& Clump::getCategory() const {
    return category;
}

inline const vector<C_Polyhedron>& Clump::getPolysVec() const {
    return vecPolys;
}

inline void Clump::resetIter() {
    iter = 0;
}

inline bool Clump::has_next() {
    return (vecPolys.size() > 0) && (iter < (int)vecPolys.size());
}

inline C_Polyhedron& Clump::getReference() {
    if (iter < 0) {
        // This should not happen.
        // I suck.
        cerr << " Sloppy programming pays off.. Invariants could be lost!!"
             << endl;
        return vecPolys[0];
    }

    return vecPolys[iter];
}

inline C_Polyhedron& Clump::getReference(int index) {
    if (index < 0) {
        // This should not happen.
        // I suck.
        cerr << " Sloppy programming pays off.. Invariants could be lost!!"
             << endl;
        return vecPolys[0];
    }

    return vecPolys[index];
}

inline void Clump::next() {
    iter++;
}

// print the clump
// ostream & operator << (ostream & in, Clump const & cl);

#endif
