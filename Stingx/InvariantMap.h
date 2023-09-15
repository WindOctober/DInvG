
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
 * Filename: InvariantMap
 * Author: Sriram Sankaranarayanan<srirams@theory.stanford.edu>
 * Comments: A map between location names and polyhedra. For CH79 and BHRZ03
 * invariants. Copyright: Please see README file.
 */

#ifndef D__INVARIANT__MAP__H_
#define D__INVARIANT__MAP__H_
#include <iostream>
#include <map>
#include <string>
#include <vector>

#include "Clump.h"
#include "Context.h"
#include "Expression.h"
#include "ExpressionStore.h"
#include "LinTransform.h"
#include "Location.h"
#include "TransitionRelation.h"
#include "ppl.hh"
#include "var-info.h"

using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;

typedef map<string, C_Polyhedron> StringPolyMap;
typedef pair<string, C_Polyhedron> StringPolyPair;

class InvariantMap {
   protected:
    /*  Members:
     *   f_ : printing info
     *   n_: dimensions
     *  nloc_ : # of locations
     *  vloc_: vector of location references
     *  varCoef : the actual map
     */
    var_info* f_;
    int n_;
    int nloc_;
    vector<Location*> const& vloc_;
    StringPolyMap varCoef;

    // is there a location with name
    bool entry_exists(string const& name) const;
    // add a pair to the map.
    void add_value_to_map(string const& str, C_Polyhedron const& what);
    // protected constructor
    InvariantMap(vector<Location*> const& vloc)
        : nloc_(vloc.size()), vloc_(vloc) {}

   public:
    // will compute the initial map
    // set each locations poly to its initial condition.

    InvariantMap(var_info* info, vector<Location*> const& vloc);

    // accessors by location pointer and name
    C_Polyhedron& operator[](Location const* l);
    C_Polyhedron& operator[](string const& what);
    // constant references
    C_Polyhedron const& operator()(Location const* l) const;
    C_Polyhedron const& operator()(string const& what) const;
    // access members

    var_info* get_var_info() const { return f_; }

    int get_dimension() const { return n_; }

    int get_num_locations() const { return nloc_; }

    StringPolyMap const& get_map_reference() const { return varCoef; }

    StringPolyMap& get_map_reference() { return varCoef; }

    // widen this wrt im CH79
    void H79_widening_assign(InvariantMap const& im);
    // widen wrt BHRZ03
    void BHRZ03_widening_assign(InvariantMap const& im);

    // assign one map into another
    void assign(InvariantMap const& im);

    // are the maps equal (check logical equivalence of polyhedra)

    bool equals(InvariantMap const& im) const;

    void print(ostream& out) const;

    // check that the map is an inductive map.
    bool check_consecution(vector<TransitionRelation*>* vrels) const;
};

ostream& operator<<(ostream& out, InvariantMap const& what);
#endif
