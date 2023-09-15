
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

#include "Clump.h"

#include "Macro.h"
#include "PolyUtils.h"

extern int clump_prune_count;
extern int bang_count;
extern int single_pre_prune_bang_count;

void Clump::initialize() {
    gli = 0;
}
void Clump::initialize(var_info* dualInfo) {
    dual_num = dualInfo->get_dimension();
    this->dualInfo = dualInfo;
    gli = 0;
}
void Clump::initialize(var_info* dualInfo, string name, string category) {
    dual_num = dualInfo->get_dimension();
    this->dualInfo = dualInfo;
    gli = 0;
    this->name = name;
    this->category = category;
}

void Clump::print_vector_of_poly() {
    int clump_poly_count = 0;
    for (vector<C_Polyhedron>::iterator j = poly_clump.begin(); j < poly_clump.end(); j++) {
        cout << endl << "clump_poly_count is " << ++clump_poly_count;
        cout << endl << (*j) << endl;
    }
    return;
}

void Clump::replace_vp(vector<C_Polyhedron> new_vp) {
    poly_clump = new_vp;
}

Clump::Clump() {
    initialize();
}
Clump::Clump(var_info* dualInfo) {
    initialize(dualInfo);
}
Clump::Clump(var_info* dualInfo, string name, string category) {
    initialize(dualInfo, name, category);
}

int Clump::get_count() {
    return poly_clump.size();
}

void Clump::insert(C_Polyhedron const& p) {
    vector<C_Polyhedron>::iterator vi;

    for (vi = poly_clump.begin(); vi < poly_clump.end(); ++vi) {
        if ((*vi).contains(p)) {
            cout << endl << "Redundant: this contains new";
            return;
        } else if (p.contains(*vi)) {
            cout << endl << "Back Prune: new contains one of this";
            vi = poly_clump.erase(vi);
            vi--;
        }
    }

    poly_clump.push_back(p);
    return;
}

vector<int> Clump::insert_with_erase_index(C_Polyhedron const& p) {
    vector<int> erase_index;
    vector<int>::reverse_iterator vi;
    int i;

    for (i = 0; i < (int)poly_clump.size(); ++i) {
        if (poly_clump[i].contains(p)) {
            cout << endl << "Redundant: (*vi).contains(p)";
        } else if (p.contains(poly_clump[i])) {
            // cout<<endl<<"p.contains(*vi)";
            cout << endl
                 << "Above part, the " << i + 1
                 << "th poly is erased by next poly in back-prune";
            erase_index.push_back(i);
            bang_count++;
            single_pre_prune_bang_count++;
        }
    }
    for (vi = erase_index.rbegin(); vi < erase_index.rend(); vi++) {
        poly_clump.erase(poly_clump.begin() + (*vi));
    }

    poly_clump.push_back(p);
    return erase_index;
}

vector<int> Clump::prune_all(C_Polyhedron& p) {
    vector<int> node_gli;
    vector<int>::iterator vi;
    cout << endl << "prune";
    int i;
    for (i = 0; i < (int)poly_clump.size(); ++i) {
        if (p.contains(poly_clump[i])) {
            clump_prune_count++;
            node_gli.push_back(i);
            cout << " clump_prune_count++, gli: " << gli << " i: " << i;
        }
    }
    for (vi = node_gli.begin(); vi < node_gli.end(); vi++) {
        poly_clump.erase(poly_clump.begin() + (*vi));
        if (gli > (*vi)) {
            gli--;
        }
    }
    cout << " " << get_category() << "::" << get_name();

    return node_gli;
}

vector<int> Clump::prune_target(C_Polyhedron& p, int target_gli) {
    vector<int> node_gli;
    vector<int>::iterator vi;
    cout << endl << "prune";
    int i = target_gli;
    // for (i=0; i < (int) vp.size(); ++i){
    if (p.contains(poly_clump[i])) {
        clump_prune_count++;
        node_gli.push_back(i);
        cout << " clump_prune_count++, gli: " << gli << " i: " << i;
    }
    //}
    for (vi = node_gli.begin(); vi < node_gli.end(); vi++) {
        poly_clump.erase(poly_clump.begin() + (*vi));
        if (gli > (*vi)) {
            gli--;
        }
    }
    cout << " " << get_category() << "::" << get_name();

    return node_gli;
}

bool Clump::contains(C_Polyhedron& poly) {
    for (auto vi = poly_clump.begin(); vi < poly_clump.end(); ++vi) {
        if ((*vi).contains(poly))
            return true;
    }
    return false;
}