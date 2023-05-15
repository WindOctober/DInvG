
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
     * dual_num = num of dual dimensions (depends on what mode the
     *                              analyzer is operated in )
     * dual_info = var_info for dual -- standard pointer for printing purposes
     *                            that should not be touched
     * vp = vector of polyhedra
     *
     * gli = a pointer to some position in vp.. some sort of a poor
     *        man's iterator. In a future version, this will be made into a
     *        full fledged iterator. Do not see the need for that now.
     *
     */

    int dual_num;
    var_info* dual_info;
    vector<C_Polyhedron> poly_clump;
    int gli;

    string name;
    string category;

    // added by Hongming - 2022/10/21
    void initialize();
    // Sriram - Aug 2004 - Old Code: PWC.
    void initialize(var_info* dual_info);
    // added by Hongming - Sept 2021
    void initialize(var_info* dual_info, string name, string category);

   public:
    // added by Hongming
    int get_gli();
    int size();
    int space_dimension() const { return poly_clump[0].space_dimension(); }

    // added by Hongming
    void print_vector_of_poly();
    const string& get_name() const;
    const string& get_category() const;
    const vector<C_Polyhedron>& get_vp() const;
    void replace_vp(vector<C_Polyhedron> new_vp);

    Clump();
    Clump(var_info* dual_info);
    Clump(var_info* dual_info, string name, string category);

    int get_count();

    // Insert a polyhedron
    void insert(C_Polyhedron const& p);
    //    added by Hongming
    vector<int> insert_with_erase_index(C_Polyhedron const& p);

    // Remove any polyhedron that is contained inside dualp
    // Sriram - Aug 2004 - Old Code: PWC.
    // modified by Hongming - Dec 2021
    vector<int> prune_all(C_Polyhedron& dualp);
    vector<int> prune_target(C_Polyhedron& dualp, int target_gli);

    // Is there a disjunct that contains "what"
    bool contains(C_Polyhedron& what);

    // operations on gli -- the java style is just co-incidental. ;-)
    // self-explanatory :-)

    void clear();

    bool has_next();

    C_Polyhedron& get_reference();
    C_Polyhedron& get_reference(int index);

    void next();
};

inline int Clump::get_gli() {
    return gli;
}
inline int Clump::size() {
    return poly_clump.size();
}

inline const string& Clump::get_name() const {
    return name;
}

inline const string& Clump::get_category() const {
    return category;
}

inline const vector<C_Polyhedron>& Clump::get_vp() const {
    return poly_clump;
}

inline void Clump::clear() {
    gli = 0;
}

inline bool Clump::has_next() {
    return (poly_clump.size() > 0) && (gli < (int)poly_clump.size());
}

inline C_Polyhedron& Clump::get_reference() {
    if (gli < 0) {
        // This should not happen.
        // I suck.
        cerr << " Sloppy programming pays off.. Invariants could be lost!!"
             << endl;
        return poly_clump[0];
    }

    return poly_clump[gli];
}

inline C_Polyhedron& Clump::get_reference(int index) {
    if (index < 0) {
        // This should not happen.
        // I suck.
        cerr << " Sloppy programming pays off.. Invariants could be lost!!"
             << endl;
        return poly_clump[0];
    }

    return poly_clump[index];
}

inline void Clump::next() {
    gli++;
}

// print the clump
// ostream & operator << (ostream & in, Clump const & cl);

#endif
