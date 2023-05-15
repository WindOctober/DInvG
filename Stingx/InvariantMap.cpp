
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

#include "InvariantMap.h"

#include "Timer.h"
#include "myassertions.h"

bool InvariantMap::entry_exists(string const& what) const {
    // check using STL routine
    return (map_ration.find(what) != map_ration.end());
}

void InvariantMap::add_value_to_map(string const& what,
                                    C_Polyhedron const& poly) {
    // first see if it is already there
    // if so raise hell about it

    PRECONDITION(!entry_exists(what),
                 "InvariantMap::add_value_to_map ---> Entry "
                     << what << " Already exists in the map" << endl);

    // now add it
    map_ration.insert(StringPolyPair(what, poly));
}

InvariantMap::InvariantMap(var_info* info, vector<Location*> const& vloc)
    : f_(info), n_(info->get_dimension()), nloc_(vloc.size()), vloc_(vloc) {
    // now construct the string map
    vector<Location*>::const_iterator vi;

    // iterate through the locations
    for (vi = vloc.begin(); vi < vloc.end(); ++vi) {
        // add the initial conditions if they exist, else add false.
        if ((*vi)->initial_poly_set())
            add_value_to_map((*vi)->get_name(), (*vi)->get_poly_reference());
        else
            add_value_to_map((*vi)->get_name(), C_Polyhedron(n_, EMPTY));
    }

    return;
}

C_Polyhedron& InvariantMap::operator[](Location const* l) {
    string const& what = l->get_name();
    /* this is checked anyway
    PRECONDITION ( (entry_exists(what)),   "InvariantMap::operator[] --> entry
    does not exist");
    */
    return (*this)[what];
}

C_Polyhedron& InvariantMap::operator[](string const& what) {
    StringPolyMap::iterator vi = map_ration.find(what);
    PRECONDITION((vi != map_ration.end()),
                 "InvariantMap::operator[] --> entry does not exist");

    return (*vi).second;
}

C_Polyhedron const& InvariantMap::operator()(Location const* l) const {
    string const& what = l->get_name();
    /* this is checked anyway
    PRECONDITION ( (entry_exists(what)),   "InvariantMap::operator[] --> entry
    does not exist");
    */
    return operator()(what);
}

C_Polyhedron const& InvariantMap::operator()(string const& what) const {
    StringPolyMap::const_iterator vi = map_ration.find(what);

    PRECONDITION((vi != map_ration.end()),
                 "InvariantMap::operator() --> entry does not exist");

    return (*vi).second;
}

void InvariantMap::H79_widening_assign(InvariantMap const& im) {
    // iterate through each string and obtain the polyhedron corresponding to
    // it. perform a H79 widening for it

    vector<Location*>::const_iterator vi;

    for (vi = vloc_.begin(); vi != vloc_.end(); ++vi) {
        // obtain a name and a polyhedron
        string const& name = (*vi)->get_name();
        C_Polyhedron const& poly = im(name);
        C_Polyhedron& my_poly = operator[](name);
        // do the widening
        // Constraint_System cs = my_poly.constraints();
        my_poly.H79_widening_assign(poly);
    }

    return;
}

void InvariantMap::BHRZ03_widening_assign(InvariantMap const& im) {
    // iterate through each string and obtain the polyhedron corresponding to
    // it. perform a BHRZ03 widening for it

    vector<Location*>::const_iterator vi;

    for (vi = vloc_.begin(); vi != vloc_.end(); ++vi) {
        // obtain a name and a polyhedron
        string const& name = (*vi)->get_name();
        C_Polyhedron const& poly = im(name);
        C_Polyhedron& my_poly = operator[](name);
        // do the widening
        my_poly.BHRZ03_widening_assign(poly);
    }

    return;
}

void InvariantMap::assign(InvariantMap const& im) {
    PRECONDITION(im.get_dimension() == n_,
                 " InvariantMap::assign -- dimension mismatch");

    vector<Location*>::const_iterator vi;
    for (vi = vloc_.begin(); vi != vloc_.end(); ++vi) {
        // obtain a name and a polyhedron
        string const& name = (*vi)->get_name();
        C_Polyhedron const& poly = im(name);
        C_Polyhedron& my_poly = operator[](name);

        my_poly = poly;  // replace my_poly.. and we are done
    }

    return;
}

void InvariantMap::print(ostream& out) const {
    StringPolyMap::const_iterator vi;

    for (vi = map_ration.begin(); vi != map_ration.end(); ++vi) {
        string const& what = (*vi).first;
        C_Polyhedron const& poly = (*vi).second;

        out << "Location: " << what << endl;
        out << "[[ " << endl;
        print_polyhedron(out, poly, f_);
        out << "]]" << endl;
    }

    return;
}

bool InvariantMap::equals(InvariantMap const& im) const {
    StringPolyMap::const_iterator vi;

    for (vi = map_ration.begin(); vi != map_ration.end(); ++vi) {
        string const& what = (*vi).first;
        C_Polyhedron const& poly1 = (*vi).second;
        C_Polyhedron const& poly2 = im(what);
        // check logical equivalence
        if (!poly1.contains(poly2) || !poly2.contains(poly1))
            return false;
    }

    return true;
}

ostream& operator<<(ostream& out, InvariantMap const& what) {
    what.print(out);
    return out;
}

bool InvariantMap::check_consecution(vector<TransitionRelation*>* vrels) const {
    vector<TransitionRelation*>::iterator vi;

    bool retval = true;

    // iterate through the transitions
    for (vi = vrels->begin(); vi != vrels->end(); ++vi) {
        string const& pr = (*vi)->get_preloc_name();
        string const& po = (*vi)->get_postloc_name();
        // obtain the pre and post polys
        C_Polyhedron const& pre_poly = operator()(pr);
        C_Polyhedron const& post_poly = operator()(po);

        C_Polyhedron temp(n_, UNIVERSE);
        // compute post(pre, transition)
        (*vi)->compute_post_new(&pre_poly, temp);
        // this better be contained in the post poly.
        if (!post_poly.contains(temp)) {
            cerr << " ERROR --- inductive consecution check failed " << *(*vi)
                 << endl;
            retval = false;
        }
    }

    return retval;
}
