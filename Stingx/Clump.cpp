
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
extern int singlePrePrune;

void Clump::initialize() {
    gli = 0;
}
void Clump::initialize(var_info* coefInfo) {
    coefNum = coefInfo->getDim();
    this->coefInfo = coefInfo;
    gli = 0;
}
void Clump::initialize(var_info* coefInfo, string name, string category) {
    coefNum = coefInfo->getDim();
    this->coefInfo = coefInfo;
    gli = 0;
    this->name = name;
    this->category = category;
}

void Clump::printPolys() {
    int PolyNo = 0;
    for (vector<C_Polyhedron>::iterator it = polysClump.begin(); it < polysClump.end(); it++) {
        cout << endl << "PolyNo is " << ++PolyNo;
        cout << endl << (*it) << endl;
    }
    return;
}

void Clump::replace_vp(vector<C_Polyhedron> new_vp) {
    polysClump = new_vp;
}

Clump::Clump() {
    initialize();
}
Clump::Clump(var_info* coefInfo) {
    initialize(coefInfo);
}
Clump::Clump(var_info* coefInfo, string name, string category) {
    initialize(coefInfo, name, category);
}

int Clump::getCount() {
    return polysClump.size();
}

void Clump::insert(C_Polyhedron const& p) {
    vector<C_Polyhedron>::iterator vi;

    for (vi = polysClump.begin(); vi < polysClump.end(); ++vi) {
        if ((*vi).contains(p)) {
            cout << endl << "Redundant: this contains new";
            return;
        } else if (p.contains(*vi)) {
            cout << endl << "Back Prune: new contains one of this";
            vi = polysClump.erase(vi);
            vi--;
        }
    }

    polysClump.push_back(p);
    return;
}

vector<int> Clump::insert_with_erase_index(C_Polyhedron const& p) {
    vector<int> erase_index;
    vector<int>::reverse_iterator vi;
    int i;

    for (i = 0; i < (int)polysClump.size(); ++i) {
        if (polysClump[i].contains(p)) {
            cout << endl << "Redundant: (*vi).contains(p)";
        } else if (p.contains(polysClump[i])) {
            // cout<<endl<<"p.contains(*vi)";
            cout << endl
                 << "Above part, the " << i + 1
                 << "th poly is erased by next poly in back-prune";
            erase_index.push_back(i);
            bang_count++;
            singlePrePrune++;
        }
    }
    for (vi = erase_index.rbegin(); vi < erase_index.rend(); vi++) {
        polysClump.erase(polysClump.begin() + (*vi));
    }

    polysClump.push_back(p);
    return erase_index;
}

vector<int> Clump::prune_all(C_Polyhedron& p) {
    vector<int> node_gli;
    vector<int>::iterator vi;
    cout << endl << "prune";
    int i;
    for (i = 0; i < (int)polysClump.size(); ++i) {
        if (p.contains(polysClump[i])) {
            clump_prune_count++;
            node_gli.push_back(i);
            cout << " clump_prune_count++, gli: " << gli << " i: " << i;
        }
    }
    for (vi = node_gli.begin(); vi < node_gli.end(); vi++) {
        polysClump.erase(polysClump.begin() + (*vi));
        if (gli > (*vi)) {
            gli--;
        }
    }
    cout << " " << get_category() << "::" << getName();

    return node_gli;
}

vector<int> Clump::prune_target(C_Polyhedron& p, int target_gli) {
    vector<int> node_gli;
    vector<int>::iterator vi;
    cout << endl << "prune";
    int i = target_gli;
    // for (i=0; i < (int) polys.size(); ++i){
    if (p.contains(polysClump[i])) {
        clump_prune_count++;
        node_gli.push_back(i);
        cout << " clump_prune_count++, gli: " << gli << " i: " << i;
    }
    //}
    for (vi = node_gli.begin(); vi < node_gli.end(); vi++) {
        polysClump.erase(polysClump.begin() + (*vi));
        if (gli > (*vi)) {
            gli--;
        }
    }
    cout << " " << get_category() << "::" << getName();

    return node_gli;
}

bool Clump::contains(C_Polyhedron& poly) {
    for (auto vi = polysClump.begin(); vi < polysClump.end(); ++vi) {
        if ((*vi).contains(poly))
            return true;
    }
    return false;
}