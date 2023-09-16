
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
     * polysClump = vector of polyhedra
     *
     * gli = a pointer to some position in polys.. some sort of a poor
     *        man's iterator. In a future version, this will be made into a
     *        full fledged iterator. Do not see the need for that now.
     *
     */

    int coefNum;
    var_info* coefInfo;
    vector<C_Polyhedron> polysClump;
    int gli;

    string name;
    string category;

    void initialize();
    void initialize(var_info* coefInfo);
    void initialize(var_info* coefInfo, string name, string category);

   public:
    int get_gli();
    int size();
    int space_dimension() const { return polysClump[0].space_dimension(); }

    void printPolys();
    const string& get_name() const;
    const string& get_category() const;
    const vector<C_Polyhedron>& get_vp() const;
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

    // operations on gli -- the java style is just co-incidental. ;-)
    // self-explanatory :-)

    void clear();

    bool has_next();

    C_Polyhedron& getReference();
    C_Polyhedron& getReference(int index);

    void next();
};

inline int Clump::get_gli() {
    return gli;
}
inline int Clump::size() {
    return polysClump.size();
}

inline const string& Clump::get_name() const {
    return name;
}

inline const string& Clump::get_category() const {
    return category;
}

inline const vector<C_Polyhedron>& Clump::get_vp() const {
    return polysClump;
}

inline void Clump::clear() {
    gli = 0;
}

inline bool Clump::has_next() {
    return (polysClump.size() > 0) && (gli < (int)polysClump.size());
}

inline C_Polyhedron& Clump::getReference() {
    if (gli < 0) {
        // This should not happen.
        // I suck.
        cerr << " Sloppy programming pays off.. Invariants could be lost!!"
             << endl;
        return polysClump[0];
    }

    return polysClump[gli];
}

inline C_Polyhedron& Clump::getReference(int index) {
    if (index < 0) {
        // This should not happen.
        // I suck.
        cerr << " Sloppy programming pays off.. Invariants could be lost!!"
             << endl;
        return polysClump[0];
    }

    return polysClump[index];
}

inline void Clump::next() {
    gli++;
}

// print the clump
// ostream & operator << (ostream & in, Clump const & cl);

#endif
