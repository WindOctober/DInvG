
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

#include "Tree.h"

#include "Macro.h"

extern int dimension;
extern var_info *info, *coefInfo, *lambdaInfo;
extern vector<Location*>* locList;
extern vector<TransitionRelation*>* transList;
extern int getTransIndex(string name);
extern bool backtrack_flag;
extern C_Polyhedron* trivial;
extern int totalPrunedCnt;
extern int singlePrePrune;
extern int prunedCnt;
extern int totalSuccessCnt;
extern int successCnt;
extern Timer TotalTimer;
extern Timer collectTimer;
extern int total_time;
extern int collect_time;
extern int singleCollect;
extern int backtrack_count;
extern int backtrack_success;
extern int merge_count;
extern int bang_count_in_merge;
extern Counter counter;
extern Timer single_merge_sub_sequences_timer;
extern void collectInv(int curId, C_Polyhedron& poly, C_Polyhedron& invd);
extern void ResetLocInv();
extern void PrintLocs();
extern bool print_tree;

void Tree::initialize(vector<Clump>& clumps) {
    this->clumps = clumps;
}

Tree::Tree() {
    ;
}

Tree::Tree(vector<Clump>& clumps) {
    initialize(clumps);
}

void Tree::set_tree(vector<Clump>& clumps) {
    initialize(clumps);
}

void Tree::set_ra(int amount) {
    ra = amount;
}
void Tree::set_er(int amount) {
    er = amount;
}
void Tree::set_unra(int amount) {
    unra = amount;
}
void Tree::set_uner(int amount) {
    uner = amount;
}
void Tree::setCurId(int index) {
    curId = index;
}
void Tree::setMaxPolyNum() {
    int res = -1;
    for (auto it = clumps.begin(); it < clumps.end(); it++) {
        if (it->size() > res) {
            res = it->size();
        }
    }

    maxPolyNum = res;
    return;
}

void Tree::ReorderClumpsPrior(vector<Clump>& clumps) {
    vector<int> relatedLocId;
    vector<int> unrelatedLocId;
    vector<int> relatedTransId;
    vector<int> unrelatedTransId;
    vector<int> targetId;

    string target = (*locList)[curId]->getName();
    int transition_index;
    string transPreLocName, transPostLocName;

    int j = 0;
    for (auto it = clumps.begin(); it < clumps.end(); it++) {
        if (it->get_category() == "Transition") {
            transition_index = getTransIndex(it->getName());
            transPreLocName = (*transList)[transition_index]->getPreLocName();
            transPostLocName = (*transList)[transition_index]->getPostLocName();
            if (transPreLocName == target || transPostLocName == target) {
                relatedTransId.push_back(j);
            } else {
                unrelatedTransId.push_back(j);
            }
        } else if (it->get_category() == "Location") {
            if (it->getName() == target) {
                relatedLocId.push_back(j);
            } else {
                unrelatedLocId.push_back(j);
            }
        }
        j++;
    }

    set_ra(relatedLocId.size());
    set_er(relatedTransId.size());
    set_unra(unrelatedLocId.size());
    set_uner(unrelatedTransId.size());

    targetId.insert(targetId.end(), unrelatedLocId.begin(),
                    unrelatedLocId.end());
    targetId.insert(targetId.end(), unrelatedTransId.begin(),
                    unrelatedTransId.end());
    targetId.insert(targetId.end(), relatedTransId.begin(),
                    relatedTransId.end());
    targetId.insert(targetId.end(), relatedLocId.begin(), relatedLocId.end());
    vector<Clump> orderedClumps;
    for (int i = 0; i < clumps.size(); i++) {
        orderedClumps.push_back(clumps[targetId[i]]);
    }

    set_tree(orderedClumps);
}

void Tree::extract_vcl_for_one_location_about_intra(vector<Clump>& clumps) {
    vector<int> relatedLocId;
    vector<int> unrelatedLocId;
    vector<int> relatedTransId;
    vector<int> unrelatedTransId;
    vector<int> targetId;

    string target = (*locList)[curId]->getName();
    int transition_index;
    string transPreLocName, transPostLocName;

    vector<Clump>::iterator vi;

    int j = 0;
    for (vi = clumps.begin(); vi < clumps.end(); vi++) {
        if (vi->get_category() == "Transition") {
            transition_index = getTransIndex(vi->getName());
            transPreLocName = (*transList)[transition_index]->getPreLocName();
            transPostLocName = (*transList)[transition_index]->getPostLocName();
            if (transPreLocName == target || transPostLocName == target) {
                relatedTransId.push_back(j);
            } else {
                unrelatedTransId.push_back(j);
            }
        } else if (vi->get_category() == "Location") {
            if (vi->getName() == target) {
                relatedLocId.push_back(j);
            } else {
                unrelatedLocId.push_back(j);
            }
        }
        j++;
    }

    set_ra(relatedLocId.size());
    // set_er(relatedTransId.size());
    // set_unra(unrelatedLocId.size());
    // set_uner(unrelatedTransId.size());

    targetId.insert(targetId.end(), relatedLocId.begin(), relatedLocId.end());
    vector<Clump> orderedClumps;
    int rlid;
    if (targetId.size() == 1) {
        rlid = targetId[0];
    } else {
        cout << endl << "Error: There are more than one related location index";
        exit(-1);
    }
    orderedClumps.push_back(clumps[rlid]);
    set_tree(orderedClumps);
}

void Tree::Print_Prune_Tree(int depth, string weavedorbanged) {
    int dth;
    int clumpsNum = size();

    // cout<<endl;
    cout << endl
         << "( " << weavedorbanged << " Prune Tree, current length is "
         << clumpsNum - depth;
    if (weavedorbanged == "Pruned") {
        cout << endl << "( in ";
        if (clumpsNum - depth > get_ra() + get_er()) {
            cout << "unrelated transition";
        } else {
            cout << "related transition";
        }
    }

    for (dth = clumpsNum; dth > 0; dth--) {
        cout << endl << "( ";
        autoprint(clumpsNum - 1, dth - 1);
        cout << "  ⋁  ";
        for (int j = 0; j < getClump(dth - 1).getCount(); j++) {
            if (j == getClump(dth - 1).getIter() && dth > depth) {
                cout << "[" << j << "]";
            } else {
                cout << " " << j << " ";
            }
        }
        cout << " --  " << getClump(dth - 1).get_category();
        cout << ":: " << getClump(dth - 1).getName();
    }
}

void Tree::Print_Prune_Tree(int depth, int hb, int lb, string weavedorbanged) {
    int dth;
    int clumpsNum = size();

    // cout<<endl;
    cout << endl
         << "( " << weavedorbanged << " Prune Tree, current length is "
         << hb + 1 - depth;
    if (weavedorbanged == "Pruned") {
        cout << endl << "( in ";
        if (clumpsNum - depth > get_ra() + get_er()) {
            cout << "unrelated transition";
        } else {
            cout << "related transition";
        }
    }

    for (dth = clumpsNum; dth > 0; dth--) {
        cout << endl << "( ";
        autoprint(clumpsNum - 1, dth - 1);
        cout << "  ⋁  ";

        for (int j = 0; j < get_max_clump_count(); j++) {
            if (getClump(dth - 1).getCount() - 1 < j) {
                cout << "   ";
            } else if (lb <= dth - 1 && dth - 1 <= hb) {
                if (j == getClump(dth - 1).getIter() && dth > depth) {
                    cout << "[" << j << "]";
                } else {
                    cout << " " << j << " ";
                }
            } else {
                cout << " " << j << " ";
            }
        }
        /*
        // old version, without smart blank with print Prune Tree
        for (int j = 0; j < getClump(dth-1).getCount(); j++){
            if (lb <= dth-1 && dth-1 <= hb){
                if (j == getClump(dth-1).getIter() && dth > depth){
                    cout<<"["<<j<<"]";
                }
                else {
                    cout<<" "<<j<<" ";
                }
            }
            else {
                cout<<" "<<j<<" ";
            }
        }
        */
        cout << " --  b: "
             << counter.get_pre_pbc_about_location_and_depth(get_target_index(),
                                                             dth - 1);
        cout << " --  " << getClump(dth - 1).get_category();
        if (getClump(dth - 1).get_category() == "Location") {
            cout << "_Intra";
        } else if (getClump(dth - 1).get_category() == "Transition") {
            cout << "_Inter";
        } else {
            cout << "Neither Location nor Transition!!!";
        }
        cout << ":: " << getClump(dth - 1).getName();
    }
}

void Tree::Print_Prune_Sequence_Tree(vector<int> sequence,
                                     int depth,
                                     string weavedorbanged) {
    int dth, i;
    int clumpsNum = size();

    // cout<<endl;
    cout << endl
         << "( " << weavedorbanged << " Prune Tree, current length is "
         << clumpsNum - depth;
    if (weavedorbanged == "Pruned") {
        cout << endl << "( in ";
        if (clumpsNum - depth > get_ra() + get_er()) {
            cout << "unrelated transition";
        } else {
            cout << "related transition";
        }
    }

    i = 0;
    for (dth = clumpsNum; dth > 0; dth--) {
        cout << endl << "( ";
        autoprint(clumpsNum - 1, dth - 1);
        cout << "  ⋁  ";

        for (int j = 0; j < get_max_clump_count(); j++) {
            if (getClump(dth - 1).getCount() - 1 < j) {
                cout << "   ";
            } else if (j == sequence[i] && dth > depth) {
                cout << "[" << j << "]";
            } else {
                cout << " " << j << " ";
            }
        }
        cout << " --  b: "
             << counter.get_pst_pbc_about_location_and_depth(get_target_index(),
                                                             dth - 1);
        cout << " --  " << getClump(dth - 1).get_category();
        cout << ":: " << getClump(dth - 1).getName();
        i++;
    }
}

void Tree::Print_Prune_Sequence_Tree(vector<int> sequence,
                                     int depth,
                                     int hb,
                                     int lb,
                                     string weavedorbanged) {
    int dth, i;
    int clumpsNum = size();

    // cout<<endl;
    cout << endl
         << "( " << weavedorbanged << " Prune Tree, current length is "
         << hb + 1 - depth;
    if (weavedorbanged == "Pruned") {
        cout << endl << "( in ";
        if (clumpsNum - depth > get_ra() + get_er()) {
            cout << "unrelated transition";
        } else {
            cout << "related transition";
        }
    }

    i = 0;
    for (dth = clumpsNum; dth > 0; dth--) {
        cout << endl << "( ";
        autoprint(clumpsNum - 1, dth - 1);
        cout << "  ⋁  ";
        for (int j = 0; j < getClump(dth - 1).getCount(); j++) {
            if (lb <= dth - 1 && dth - 1 <= hb) {
                if (j == sequence[i] && dth > depth) {
                    cout << "[" << j << "]";
                } else {
                    cout << " " << j << " ";
                }
            } else {
                cout << " " << j << " ";
            }
        }
        cout << " --  " << getClump(dth - 1).get_category();
        cout << ":: " << getClump(dth - 1).getName();
        if (lb <= dth - 1 && dth - 1 <= hb) {
            i++;
        }
    }
}

void Tree::prune_node_self_inspection(int curId, C_Polyhedron& invd) {
    int dth = size() - 1;
    vector<Clump>::iterator vi;

    store_clumps_gli();
    clear_pruned_node();
    // for (; dth>=0/*clumps.size()-ra-er*/; dth--){
    vi = clumps.begin() + dth;
    // vector<int> node_gli = (*vi).prune_all(invd);
    vector<int> node_gli = (*vi).prune_target(invd, clumps_gli[dth]);
    if (node_gli.size()) {
        insert_pruned_node(dth, node_gli);
        backtrack_flag = false;
    }
    //}
    store_conflict_node();
    dth = first_conflict;
    while (dth-- > 0) {
        vi = clumps.begin() + dth;
        (*vi).resetIter();
        cout << endl
             << "depth: " << dth
             << ", clear_lower_gli, iter : " << (*vi).getIter() << " "
             << (*vi).get_category() << "::" << (*vi).getName();
    }
}

void Tree::insert_pruned_node(int depth, vector<int> node_gli) {
    pruned_node.emplace_back(depth, node_gli);
}

void Tree::store_conflict_node() {
    vector<pair<int, vector<int>>>::iterator vi;
    vector<int> node_gli;
    vector<int>::iterator it;
    // vector<int> new_conflict_depth;
    int depth;

    conflict_depth.clear();
    for (vi = pruned_node.begin(); vi < pruned_node.end(); vi++) {
        depth = (*vi).first;
        node_gli = (*vi).second;

        it = find(node_gli.begin(), node_gli.end(), clumps_gli[depth]);
        if (it != node_gli.end()) {
            conflict_depth.push_back(depth);
        }
    }
    // conflict_depth = new_conflict_depth;
    if (conflict_depth.size() != 0) {
        first_conflict = *conflict_depth.begin();
    } else {
        first_conflict = -1;
    }

    return;
}

void Tree::store_clumps_gli() {
    int dth;
    vector<Clump>::iterator vi;
    // vector<int> new_clumps_gli;
    clumps_gli.clear();
    for (dth = 0; dth < size(); dth++) {
        vi = clumps.begin() + dth;
        clumps_gli.push_back((*vi).getIter());
    }
    // clumps_gli = new_clumps_gli;
}

void Tree::prune_clumps_by_hierarchy_inclusion() {
    cout << endl;
    cout << endl << "> > > prune_clumps_by_hierarchy_inclusion()";
    vector<Clump>::iterator vi;
    vector<C_Polyhedron>::iterator vj;
    vector<Location> tr_union;
    vector<Location>::iterator vk;

    // initialize union
    for (vi = clumps.begin(); vi < clumps.end(); vi++) {
        Location clumps_union(dimension, info, coefInfo, lambdaInfo,
                              "union_" + (*vi).getName(),
                              curId * (dimension + 1));
        tr_union.push_back(clumps_union);
    }
    for (vk = tr_union.end() - 1; vk >= tr_union.begin(); vk--) {
        cout << (*vk);
    }

    // build up union for each hierarchy
    int dth = tr_union.size() - 1;
    while (dth >= 0) {
        vk = tr_union.begin() + dth;
        Clump cl = clumps[dth];
        C_Polyhedron clumps_poly(coefInfo->getDim(), UNIVERSE);
        int i = 0;
        for (i = 0; i < cl.getCount(); i++) {
            cout << endl << "to extract invariant";
            (*vk).ExtractInv(cl.getReference(i).minimized_constraints());

            cout << endl << "to update constraints";
            (*vk).UpdateCoefCS(clumps_poly);
        }
        cout << endl << "dth: " << dth << ", " << (*vk).getName();
        cout << endl << "this union of clumps poly: " << clumps_poly;
        dth--;
    }
    for (vk = tr_union.end() - 1; vk >= tr_union.begin(); vk--) {
        cout << (*vk);
    }

    // take each "iter" from polys[iter] and test inclusion for polys[iter] and
    // other hierarchy union

    cout << endl << "< < < prune_clumps_by_hierarchy inclusion()";
}

vector<vector<vector<int>>> Tree::sequences_generation(
    string divide_into_sections,
    C_Polyhedron& initp) {
    cout << endl << "> > > Tree::sequences generation()";

    vector<vector<vector<int>>> sequences;

    if (divide_into_sections == "one_per_group") {
        sequences = one_per_group(initp);
    } else if (divide_into_sections == "two_per_group") {
        sequences = two_per_group(initp);
    } else if (divide_into_sections == "three_per_group") {
        sequences = three_per_group(initp);
    } else if (divide_into_sections == "four_per_group") {
        sequences = four_per_group(initp);
    } else if (divide_into_sections == "divide_target_into_double") {
        sequences = divide_target_into_double(initp);
    } else if (divide_into_sections == "divide_by_inter_transition") {
        sequences = divide_by_inter_transition(initp);
    } else if (divide_into_sections == "divide_prior2_into_four") {
        sequences = divide_prior2_into_four(initp);
    } else {
        cout << endl << "divide_into_sections: wrong type";
    }

    cout << endl << "< < < Tree::sequences generation()";
    return sequences;
}

vector<vector<vector<int>>> Tree::divide_by_target_relation(
    C_Polyhedron& initp) {
    cout << endl << "> > > Tree::divide_by_target_relation()";
    vector<vector<vector<int>>> sequences;

    int clumpsNum = clumps.size();
    vector<pair<int, int>> length_bound;
    vector<pair<int, int>>::iterator it;
    length_bound.push_back(make_pair(clumpsNum - 1, clumpsNum - ra - er + 0));
    length_bound.push_back(make_pair(clumpsNum - ra - er - 1 + 0, 0));
    for (it = length_bound.begin(); it < length_bound.end(); it++) {
        int length_hb = (*it).first;
        int length_lb = (*it).second;
        vector<vector<int>> sub_sequences;
        cout << endl;
        cout << endl << "From hb:" << length_hb << " To lb:" << length_lb;

        sub_sequences = dfs_sub_sequences_traverse(length_hb, length_lb, initp);

        cout << endl
             << "sub_sequences.size()/capacity():" << sub_sequences.size()
             << "/" << sub_sequences.capacity();
        cout << endl << "This PRE_LOC has banged:" << singlePrePrune;
        sequences.push_back(sub_sequences);
    }

    cout << endl << "< < < Tree::divide_by_target_relation()";
    return sequences;
}

vector<vector<vector<int>>> Tree::one_per_group(C_Polyhedron& initp) {
    cout << endl << "> > > Tree::one_per_group()";
    vector<vector<vector<int>>> sequences;

    int clumpsNum = clumps.size();
    vector<pair<int, int>> length_bound;
    vector<pair<int, int>>::iterator it;

    for (int i = clumpsNum - 1; i >= 0; i = i - 1) {
        length_bound.push_back(make_pair(i, i));
    }

    for (it = length_bound.begin(); it < length_bound.end(); it++) {
        int length_hb = (*it).first;
        int length_lb = (*it).second;
        vector<vector<int>> sub_sequences;
        cout << endl;
        cout << endl << "From hb:" << length_hb << " To lb:" << length_lb;

        sub_sequences = dfs_sub_sequences_traverse(length_hb, length_lb, initp);

        cout << endl
             << "sub_sequences.size()/capacity():" << sub_sequences.size()
             << "/" << sub_sequences.capacity();
        cout << endl << "This PRE_LOC has banged:" << singlePrePrune;
        sequences.push_back(sub_sequences);
    }

    cout << endl;
    cout << endl << "< < < Tree::one_per_group()";
    return sequences;
}

vector<vector<vector<int>>> Tree::two_per_group(C_Polyhedron& initp) {
    cout << endl << "> > > Tree::two_per_group()";
    vector<vector<vector<int>>> sequences;

    int clumpsNum = clumps.size();
    vector<pair<int, int>> length_bound;
    vector<pair<int, int>>::iterator it;
    if (clumpsNum % 2 == 0) {
        for (int i = clumpsNum - 1; i > 0; i = i - 2) {
            length_bound.push_back(make_pair(i, i - 1));
        }
    } else {
        int i;
        length_bound.push_back(make_pair(clumpsNum - 1, clumpsNum - 1));
        for (i = clumpsNum - 1 - 1; i > 0; i = i - 2) {
            length_bound.push_back(make_pair(i, i - 1));
        }
        if (i == 0) {
            length_bound.push_back(make_pair(0, 0));
        }
    }
    for (it = length_bound.begin(); it < length_bound.end(); it++) {
        int length_hb = (*it).first;
        int length_lb = (*it).second;
        vector<vector<int>> sub_sequences;
        cout << endl;
        cout << endl << "From hb:" << length_hb << " To lb:" << length_lb;

        sub_sequences = dfs_sub_sequences_traverse(length_hb, length_lb, initp);

        cout << endl
             << "sub_sequences.size()/capacity():" << sub_sequences.size()
             << "/" << sub_sequences.capacity();
        cout << endl << "This PRE_LOC has banged:" << singlePrePrune;
        sequences.push_back(sub_sequences);
    }

    cout << endl << "< < < Tree::two_per_group()";
    return sequences;
}

vector<vector<vector<int>>> Tree::three_per_group(C_Polyhedron& initp) {
    cout << endl << "> > > Tree::three_per_group()";
    vector<vector<vector<int>>> sequences;

    int clumpsNum = clumps.size();
    vector<pair<int, int>> length_bound;
    vector<pair<int, int>>::iterator it;

    int i = clumpsNum;
    while (i - 3 >= 0) {
        length_bound.push_back(make_pair(i - 1, i - 3));
        i = i - 3;
    }
    if (i > 0) {
        length_bound.push_back(make_pair(i - 1, 0));
    }

    for (it = length_bound.begin(); it < length_bound.end(); it++) {
        int length_hb = (*it).first;
        int length_lb = (*it).second;
        vector<vector<int>> sub_sequences;
        cout << endl;
        cout << endl << "From hb:" << length_hb << " To lb:" << length_lb;

        sub_sequences = dfs_sub_sequences_traverse(length_hb, length_lb, initp);

        cout << endl
             << "sub_sequences.size()/capacity():" << sub_sequences.size()
             << "/" << sub_sequences.capacity();
        cout << endl << "This PRE_LOC has banged:" << singlePrePrune;
        sequences.push_back(sub_sequences);
    }

    cout << endl << "< < < Tree::three_per_group()";
    return sequences;
}

vector<vector<vector<int>>> Tree::four_per_group(C_Polyhedron& initp) {
    cout << endl << "> > > Tree::four_per_group()";
    vector<vector<vector<int>>> sequences;

    int clumpsNum = clumps.size();
    vector<pair<int, int>> length_bound;
    vector<pair<int, int>>::iterator it;

    int i = clumpsNum;
    while (i - 4 >= 0) {
        length_bound.push_back(make_pair(i - 1, i - 4));
        i = i - 4;
    }
    if (i > 0) {
        length_bound.push_back(make_pair(i - 1, 0));
    }

    for (it = length_bound.begin(); it < length_bound.end(); it++) {
        int length_hb = (*it).first;
        int length_lb = (*it).second;
        vector<vector<int>> sub_sequences;
        cout << endl;
        cout << endl << "From hb:" << length_hb << " To lb:" << length_lb;

        sub_sequences = dfs_sub_sequences_traverse(length_hb, length_lb, initp);

        cout << endl
             << "sub_sequences.size()/capacity():" << sub_sequences.size()
             << "/" << sub_sequences.capacity();
        cout << endl << "This PRE_LOC has banged:" << singlePrePrune;
        sequences.push_back(sub_sequences);
    }

    cout << endl << "< < < Tree::four_per_group()";
    return sequences;
}

vector<vector<vector<int>>> Tree::divide_target_into_double(
    C_Polyhedron& initp) {
    cout << endl << "> > > Tree::divide_target_into_double()";
    vector<vector<vector<int>>> sequences;

    int clumpsNum = clumps.size();
    vector<pair<int, int>> length_bound;
    vector<pair<int, int>>::iterator it;
    int i;

    // related intra
    i = clumpsNum - 1;
    length_bound.push_back(make_pair(i, i));
    i--;
    // related inter
    for (; i > clumpsNum - (ra + er) - 1; i = i - 2) {
        length_bound.push_back(make_pair(i, i - 1));
    }
    // unrelated inter and intra
    for (; i >= 0; i = i - 1) {
        length_bound.push_back(make_pair(i, i));
    }

    for (it = length_bound.begin(); it < length_bound.end(); it++) {
        int length_hb = (*it).first;
        int length_lb = (*it).second;
        vector<vector<int>> sub_sequences;
        cout << endl;
        cout << endl << "From hb:" << length_hb << " To lb:" << length_lb;

        sub_sequences = dfs_sub_sequences_traverse(length_hb, length_lb, initp);

        cout << endl
             << "sub_sequences.size()/capacity():" << sub_sequences.size()
             << "/" << sub_sequences.capacity();
        cout << endl << "This PRE_LOC has banged:" << singlePrePrune;
        sequences.push_back(sub_sequences);
    }

    cout << endl << "< < < Tree::divide_target_into_double()";
    return sequences;
}

vector<vector<vector<int>>> Tree::divide_by_inter_transition(
    C_Polyhedron& initp) {
    cout << endl << "> > > Tree::divide_by_inter_transition()";
    vector<vector<vector<int>>> sequences;

    int clumpsNum = clumps.size();
    vector<pair<int, int>> length_bound;
    vector<pair<int, int>>::iterator it;
    int i;

    // related intra
    i = clumpsNum - ra;
    length_bound.push_back(make_pair(i, i));
    i--;
    // related and unrelated inter
    length_bound.push_back(make_pair(i, i - (er + uner) + 1));
    i = i - (er + uner) + 1 - 1;
    // unrelated intra
    length_bound.push_back(make_pair(i, 0));

    for (it = length_bound.begin(); it < length_bound.end(); it++) {
        int length_hb = (*it).first;
        int length_lb = (*it).second;
        vector<vector<int>> sub_sequences;
        cout << endl;
        cout << endl << "From hb:" << length_hb << " To lb:" << length_lb;

        sub_sequences = dfs_sub_sequences_traverse(length_hb, length_lb, initp);

        cout << endl
             << "sub_sequences.size()/capacity():" << sub_sequences.size()
             << "/" << sub_sequences.capacity();
        cout << endl << "This PRE_LOC has banged:" << singlePrePrune;
        sequences.push_back(sub_sequences);
    }

    cout << endl << "< < < Tree::divide_by_inter_transition()";
    return sequences;
}

vector<vector<vector<int>>> Tree::divide_prior2_into_four(C_Polyhedron& initp) {
    cout << endl << "> > > Tree::divide_prior2_into_four()";
    vector<vector<vector<int>>> sequences;

    int clumpsNum = clumps.size();
    vector<pair<int, int>> length_bound;
    vector<pair<int, int>>::iterator it;
    int i;

    // related intra
    i = clumpsNum - ra;
    length_bound.push_back(make_pair(i, i));
    i--;
    // related inter
    if (er != 0) {
        length_bound.push_back(make_pair(i, i - (er) + 1));
        i = i - (er) + 1 - 1;
    }
    // unrelated inter
    if (uner != 0) {
        length_bound.push_back(make_pair(i, i - (uner) + 1));
        i = i - (uner) + 1 - 1;
    }
    // unrelated intra
    length_bound.push_back(make_pair(i, 0));

    for (it = length_bound.begin(); it < length_bound.end(); it++) {
        int length_hb = (*it).first;
        int length_lb = (*it).second;
        vector<vector<int>> sub_sequences;
        cout << endl;
        cout << endl << "From hb:" << length_hb << " To lb:" << length_lb;

        sub_sequences = dfs_sub_sequences_traverse(length_hb, length_lb, initp);

        cout << endl
             << "sub_sequences.size()/capacity():" << sub_sequences.size()
             << "/" << sub_sequences.capacity();
        cout << endl << "This PRE_LOC has banged:" << singlePrePrune;
        sequences.push_back(sub_sequences);
    }

    cout << endl << "< < < Tree::divide_prior2_into_four()";
    return sequences;
}

vector<vector<vector<int>>> Tree::merge_sub_sequences(
    vector<vector<vector<int>>> sequences,
    C_Polyhedron initp) {
    cout << endl << "> > > Tree::merge_sub_sequences()";
    cout << endl << "| sequences.size(): " << sequences.size();

    vector<vector<vector<int>>> merged_sequences;

    if (sequences.size() > 2) {
        vector<vector<vector<int>>>::iterator it;
        int hb = clumps.size() - 1;
        int lb = clumps.size();
        if (sequences.size() % 2 == 0) {
            for (it = sequences.begin(); it < sequences.end(); it = it + 2) {
                hb = hb;
                lb = lb - (*(*it).begin()).size() -
                     (*(*(it + 1)).begin()).size();
                vector<vector<int>> merged_sub_sequences;
                merged_sub_sequences = Merge(*it, *(it + 1), hb, lb, initp);
                merged_sequences.push_back(merged_sub_sequences);
                hb = hb - (*(*it).begin()).size() -
                     (*(*(it + 1)).begin()).size();
                lb = lb;
            }
        } else {
            for (it = sequences.begin(); it < sequences.end() - 1;
                 it = it + 2) {
                hb = hb;
                lb = lb - (*(*it).begin()).size() -
                     (*(*(it + 1)).begin()).size();
                vector<vector<int>> merged_sub_sequences;
                merged_sub_sequences = Merge(*it, *(it + 1), hb, lb, initp);
                merged_sequences.push_back(merged_sub_sequences);
                hb = hb - (*(*it).begin()).size() -
                     (*(*(it + 1)).begin()).size();
                lb = lb;
            }
            if (it == sequences.end() - 1) {
                merged_sequences.push_back(*it);
            }
        }
        merge_count++;
    } else {
        merged_sequences = sequences;
    }

    cout << endl << "| merged_sequences.size(): " << merged_sequences.size();
    cout << endl << "< < < Tree::merge_sub_sequences()";
    return merged_sequences;
}

vector<vector<vector<int>>> Tree::merge_target_sub_sequences(
    vector<vector<vector<int>>> sequences,
    C_Polyhedron initp) {
    cout << endl << "> > > Tree::merge_target_sub_sequences()";
    cout << endl << "| sequences.size(): " << sequences.size();

    vector<vector<vector<int>>> merged_sequences;
    int clumpsNum = clumps.size();
    int curId = clumpsNum - (ra + er) - 1;

    if (sequences.size() > 2) {
        vector<vector<vector<int>>>::iterator it;
        int hb = clumps.size() - 1;
        int lb = clumps.size();
        for (it = sequences.begin(); hb > curId && it < sequences.end() - 1;
             it = it + 2) {
            hb = hb;
            lb = lb - (*(*it).begin()).size() - (*(*(it + 1)).begin()).size();
            vector<vector<int>> merged_sub_sequences;
            merged_sub_sequences = Merge(*it, *(it + 1), hb, lb, initp);
            merged_sequences.push_back(merged_sub_sequences);
            hb = hb - (*(*it).begin()).size() - (*(*(it + 1)).begin()).size();
            lb = lb;
        }
        for (; it < sequences.end(); it = it + 1) {
            merged_sequences.push_back(*it);
        }
        merge_count++;
    } else {
        merged_sequences = sequences;
    }

    cout << endl << "| merged_sequences.size(): " << merged_sequences.size();
    cout << endl << "< < < Tree::merge_target_sub_sequences()";
    return merged_sequences;
}

vector<vector<vector<int>>> Tree::merge_first_sub_sequences(
    vector<vector<vector<int>>> sequences,
    C_Polyhedron initp) {
    cout << endl << "> > > Tree::merge_first_sub_sequences()";
    cout << endl << "| sequences.size(): " << sequences.size();

    vector<vector<vector<int>>> merged_sequences;

    if (sequences.size() > 2) {
        vector<vector<vector<int>>>::iterator it;
        int hb = clumps.size() - 1;
        int lb = clumps.size();
        it = sequences.begin();
        // for (it=sequences.begin(); hb>curId && it<sequences.end()-1;
        // it=it+2){
        hb = hb;
        lb = lb - (*(*it).begin()).size() - (*(*(it + 1)).begin()).size();
        vector<vector<int>> merged_sub_sequences;
        merged_sub_sequences = Merge(*it, *(it + 1), hb, lb, initp);
        merged_sequences.push_back(merged_sub_sequences);
        // hb = hb - (*(*it).begin()).size() - (*(*(it+1)).begin()).size();
        // lb = lb;
        //}
        it = it + 2;
        for (; it < sequences.end(); it = it + 1) {
            merged_sequences.push_back(*it);
        }
        merge_count++;
    } else {
        merged_sequences = sequences;
    }

    cout << endl << "| merged_sequences.size(): " << merged_sequences.size();
    cout << endl << "< < < Tree::merge_first_sub_sequences()";
    return merged_sequences;
}

vector<vector<vector<int>>> Tree::merge_end_sub_sequences(
    vector<vector<vector<int>>> sequences,
    C_Polyhedron initp) {
    cout << endl << "> > > Tree::merge_end_sub_sequences()";
    cout << endl << "| sequences.size(): " << sequences.size();

    vector<vector<vector<int>>> merged_sequences;
    // int curId = clumpsNum-(ra+er)-1;

    if (sequences.size() > 2) {
        vector<vector<vector<int>>>::iterator it;

        for (it = sequences.begin(); it < sequences.end() - 2; it = it + 1) {
            merged_sequences.push_back(*it);
        }

        int hb = 0 - 1;
        int lb = 0;
        // for (it=sequences.begin(); hb>curId && it<sequences.end()-1;
        // it=it+2){
        hb = hb + (*(*it).begin()).size() + (*(*(it + 1)).begin()).size();
        lb = lb;
        vector<vector<int>> merged_sub_sequences;
        merged_sub_sequences = Merge(*it, *(it + 1), hb, lb, initp);
        merged_sequences.push_back(merged_sub_sequences);
        // hb = hb - (*(*it).begin()).size() - (*(*(it+1)).begin()).size();
        // lb = lb;
        //}

        merge_count++;
    } else {
        merged_sequences = sequences;
    }

    cout << endl << "| merged_sequences.size(): " << merged_sequences.size();
    cout << endl << "< < < Tree::merge_end_sub_sequences()";
    return merged_sequences;
}

vector<vector<int>> Tree::Merge(vector<vector<int>> sub_sequences1,
                                vector<vector<int>> sub_sequences2,
                                int hb,
                                int lb,
                                C_Polyhedron initp) {
    vector<vector<int>> merged_sub_sequences;
    bang_count_in_merge = 0;

    vector<vector<vector<int>>> two_sub_sequences;
    two_sub_sequences.push_back(sub_sequences1);
    two_sub_sequences.push_back(sub_sequences2);
    int start = -1;
    int depth = hb;
    vector<int> sequence;
    Clump invd_vp(coefInfo);
    single_merge_sub_sequences_timer.restart();
    // Merge_recursive(two_sub_sequences, merged_sub_sequences, start, sequence,
    // initp, invd_vp, hb, lb);
    Merge_recursive2(two_sub_sequences, merged_sub_sequences, sequence, start,
                     depth, initp, invd_vp, hb, lb);
    single_merge_sub_sequences_timer.stop();
    int single_merge_sub_sequences_time =
        single_merge_sub_sequences_timer.getElapsedTime();

    cout << endl
         << "| hb:" << hb << ", lb:" << lb
         << ", weave_in_merge:" << invd_vp.getCount()
         << ", bang_in_merge:" << bang_count_in_merge
         << ", time:" << single_merge_sub_sequences_time;
    cout << endl
         << "merged_sub_sequences.capacity():"
         << merged_sub_sequences.capacity();
    cout << endl
         << "merged_sub_sequences.size():" << merged_sub_sequences.size();
    return merged_sub_sequences;
}

void Tree::Merge_recursive2(vector<vector<vector<int>>> two_sub_sequences,
                            vector<vector<int>>& merged_sub_sequences,
                            vector<int>& sequence,
                            int i,
                            int depth,
                            C_Polyhedron& poly,
                            Clump& invd_vp,
                            int hb,
                            int lb) {
    if (i == two_sub_sequences.size() - 1) {
        // cout<<endl;
        // cout<<endl<<"/-----------------------------";
        // Print_Prune_Sequence_Tree(sequence, lb, hb, lb,"Weaved");
        collectTimer.restart();
        // collect_invariant_polys(poly, invd_vp);
        // merged_sub_sequences.push_back(sequence);
        collect_invariant_polys_and_sub_sequences(invd_vp, merged_sub_sequences,
                                                  poly, sequence);
        collectTimer.stop();
        cout << endl
             << "- The collect_invariant_polys_and_sub_sequences Time Taken "
                "(0.01s) = "
             << collectTimer.getElapsedTime();
        // cout<<endl<<"\\-----------------------------"<<endl;
        return;
    }

    int j = 0;
    vector<int> prunedSeq;
    bool prunedFlag = false;
    while (j < two_sub_sequences[i + 1].size()) {
        vector<int> s;
        s.insert(s.end(), two_sub_sequences[i + 1][j].begin(),
                 two_sub_sequences[i + 1][j].end());

        if (prunedSeq.size() > 0 && checkSeqPrefix(prunedSeq, s)) {
            j++;
            continue;
        } else {
            prunedSeq.clear();
            prunedFlag = false;
        }

        C_Polyhedron p(poly);
        int index = 0;
        vector<int> tmpSeq;
        vector<int> printedSeq = sequence;

        for (vector<int>::iterator it = s.begin(); it < s.end(); it++) {
            tmpSeq.push_back(*it);
            printedSeq.push_back(*it);
            p.intersection_assign(getClump(depth - index).getReference(*it));
            if (invd_vp.contains(p)) {
                // Print_Prune_Sequence_Tree(printedSeq, depth-index, hb, lb,
                // "Pruned");
                totalPrunedCnt++;
                singlePrePrune++;
                bang_count_in_merge++;

                prunedSeq = tmpSeq;
                prunedFlag = true;
                break;
            }
            index++;
        }

        if (prunedFlag != true) {
            Merge_recursive2(two_sub_sequences, merged_sub_sequences, printedSeq,
                             i + 1, depth - index, p, invd_vp, hb, lb);
        } else {
            ;
        }
        j++;
    }
    return;
}

vector<vector<int>> Tree::dfs_sub_sequences_traverse(int hb,
                                                     int lb,
                                                     C_Polyhedron& initp) {
    cout << endl << "> > > Tree::dfs_sub_sequences_traverse()";
    vector<vector<int>> sub_sequences;
    Clump invd_vp(coefInfo);
    int depth = hb + 1;
    dfs_sub_sequences_traverse_recursive(sub_sequences, hb, lb, depth, initp,
                                         invd_vp);

    cout << endl
         << "This sub_sequences invd_vp has weaved:" << invd_vp.getCount();
    cout << endl << "< < < Tree::dfs_sub_sequences_traverse()";
    return sub_sequences;
}

void Tree::dfs_sub_sequences_traverse_recursive(
    vector<vector<int>>& sub_sequences,
    int hb,
    int lb,
    int depth,
    C_Polyhedron& poly,
    Clump& invd_vp) {
    if (TotalTimer.getElapsedTime() >= total_time) {
        cout << endl << "Time is up!";
        return;
    }

    if (invd_vp.contains(poly)) {
        totalPrunedCnt++;
        singlePrePrune++;
        counter.set_pre_pbc_at_location_and_depth(get_target_index(), depth);
        if (print_tree) {
            Print_Prune_Tree(depth, hb, lb, "Pruned");
        }
        return;
    }

    if (depth == lb) {
        if (print_tree) {
            Print_Prune_Tree(depth, hb, lb, "Weaved");
        }
        collectTimer.restart();
        collect_invariant_polys_and_sub_sequences(invd_vp, sub_sequences, poly,
                                                  hb, lb);
        collectTimer.stop();

        return;
    }

    getClump(depth - 1).resetIter();
    while (getClump(depth - 1).has_next()) {
        // cout<<endl<<"in while...next()";
        // cout<<endl<<"depth:"<<depth<<", poly:";
        // cout<<endl<<poly;
        C_Polyhedron p(poly);
        p.intersection_assign(getClump(depth - 1).getReference());
        dfs_sub_sequences_traverse_recursive(sub_sequences, hb, lb, depth - 1,
                                             p, invd_vp);
        if (backtrack_flag == true) {
            if (invd_vp.contains(poly)) {
                backtrack_success++;
                cout << endl << "Pruned by backtracking in depth " << depth;
                getClump(depth - 1).resetIter();
                return;
            } else {
                if (backtrack_success >= 1) {
                    backtrack_count++;
                    backtrack_success = 0;
                }
                backtrack_flag = false;
            }
        }
        getClump(depth - 1).next();
    }

    // cout<<endl<<"< < < Tree::dfs_sub_sequences_traverse_recursive()";
    return;
}

void Tree::collect_invariant_polys(C_Polyhedron& poly, Clump& invd_vp) {
    invd_vp.insert(poly);
    cout << endl << "  invd_vp.size():" << invd_vp.getCount();
}

void Tree::collect_sub_sequences(vector<vector<int>>& sub_sequences,
                                 int hb,
                                 int lb) {
    // cout<<endl<<"> > > Tree::collect_sub_sequences()";

    vector<int> s;
    int dth;
    for (dth = hb; dth >= lb; dth--) {
        s.push_back(getClump(dth).getIter());
    }
    cout << endl << "- s.size():" << s.size();
    cout << endl << "  s:";
    for (int i = 0; i < s.size(); i++) {
        cout << s[i];
    }
    sub_sequences.push_back(s);
    // cout<<endl<<"< < < Tree::collect_sub_sequences()";
}

void Tree::collect_invariant_polys_and_sub_sequences(
    Clump& invd_vp,
    vector<vector<int>>& sub_sequences,
    C_Polyhedron& poly,
    int hb,
    int lb) {
    // cout<<endl<<"> > > Tree::collect_invariant_polys_and_sub_sequences()";
    vector<int> s;
    int dth;
    for (dth = hb; dth >= lb; dth--) {
        s.push_back(getClump(dth).getIter());
    }
    //  collect invd_vp
    vector<int> erase_index;
    erase_index = invd_vp.insert_with_erase_index(poly);
    // cout<<endl<<"  invd_vp.size():"<<invd_vp.getCount();

    //  add above collectors
    vector<int>::reverse_iterator vi;
    for (vi = erase_index.rbegin(); vi < erase_index.rend(); vi++) {
        sub_sequences.erase(sub_sequences.begin() + (*vi));
    }
    sub_sequences.push_back(s);

    // cout<<endl<<"< < < Tree::collect_invariant_polys_and_sub_sequences()";
    return;
}

void Tree::collect_invariant_polys_and_sub_sequences(
    Clump& invd_vp,
    vector<vector<int>>& sub_sequences,
    C_Polyhedron& poly,
    vector<int>& sequence) {
    // cout<<endl<<"> > > Tree::collect_invariant_polys_and_sub_sequences()";

    //  collect sub_sequences
    cout << endl << "- sequence.size():" << sequence.size();
    cout << endl << "  sequence:";
    for (int i = 0; i < sequence.size(); i++) {
        cout << sequence[i];
    }

    //  collect invd_vp
    vector<int> erase_index;
    erase_index = invd_vp.insert_with_erase_index(poly);
    cout << endl << "  invd_vp.size():" << invd_vp.getCount();

    //  add above collectors
    vector<int>::reverse_iterator vi;
    for (vi = erase_index.rbegin(); vi < erase_index.rend(); vi++) {
        sub_sequences.erase(sub_sequences.begin() + (*vi));
    }
    sub_sequences.push_back(sequence);

    return;
}

void Tree::treeSeqTraverse(vector<vector<vector<int>>> sequences,
                           C_Polyhedron& initp,
                           C_Polyhedron& invd) {
    cout << endl << "> > > Tree::treeSeqTraverse()";

    int start = 0;
    vector<int> sequence;
    int depth = clumps.size() - 1;
    dfsSequences(sequence, sequences, start, depth, initp, invd);
    cout << endl << "< < < Tree::treeSeqTraverse()";
}

void Tree::dfsSequences(vector<int>& sequence,
                        vector<vector<vector<int>>> sequences,
                        int i,
                        int depth,
                        C_Polyhedron& poly,
                        C_Polyhedron& invd) {
    if (TotalTimer.getElapsedTime() >= total_time) {
        cout << endl << "Time is up!";
        return;
    }
    if (i == sequences.size()) {
        totalSuccessCnt++;
        successCnt++;

        cout << endl;
        cout << endl << "sequence:";
        for (int k = 0; k < sequence.size(); k++) {
            cout << sequence[k];
        }
        cout << endl << "/-----------------------------";
        if (print_tree) {
            Print_Prune_Sequence_Tree(sequence, 0, "Weaved");
        }
        collectTimer.restart();
        collectInv(curId, poly, invd);
        cout << endl;
        cout << endl << "- Have Collected " << totalSuccessCnt << " invariant(s)";
        collectTimer.stop();
        cout << endl
             << "- The collectInv Time Taken (0.01s) = "
             << collectTimer.getElapsedTime();
        collect_time = collect_time + collectTimer.getElapsedTime();
        singleCollect = singleCollect + collectTimer.getElapsedTime();
        cout << endl << "------------------------------";
        cout << endl << "- poly: " << endl << "  " << poly;
        cout << endl << "- invd: " << endl << "  " << invd;
        cout << endl
             << "- invariant: " << endl
             << "  " << (*locList)[curId]->GetInv();
        cout << endl << "\\-----------------------------";
        return;
    }

    int j = 0;
    vector<int> prunedSeq;
    bool prunedFlag = false;
    while (j < sequences[i].size()) {
        vector<int> s;
        s.insert(s.end(), sequences[i][j].begin(), sequences[i][j].end());

        if (prunedSeq.size() > 0 && checkSeqPrefix(prunedSeq, s)) {
            j++;
            continue;
        } else {
            prunedSeq.clear();
            prunedFlag = false;
        }

        C_Polyhedron p(poly);
        int index = 0;
        vector<int> tmpSeq;
        vector<int> printedSeq = sequence;
        for (vector<int>::iterator it = s.begin(); it < s.end(); it++) {
            tmpSeq.push_back(*it);
            printedSeq.push_back(*it);
            outputPolyhedron(&getClump(depth - index).getReference(*it),coefInfo);
            p.intersection_assign(getClump(depth - index).getReference(*it));
            // exit(0);
            if (invd.contains(p)) {
                totalPrunedCnt++;
                prunedCnt++;
                counter.set_pst_pbc_at_location_and_depth(get_target_index(),
                                                          depth - index);
                if (print_tree) {
                    Print_Prune_Sequence_Tree(printedSeq, depth - index, "Pruned");
                }
                prunedSeq = tmpSeq;
                prunedFlag = true;
                break;
            }
            index++;
        }

        if (!prunedFlag) {
            dfsSequences(printedSeq, sequences, i + 1, depth - index, p, invd);
        }
        j++;
    }
    return;
}

bool Tree::checkSeqPrefix(vector<int> prunedSeq, vector<int> s) {
    for (int i = 0; i < prunedSeq.size(); i++) {
        if (prunedSeq[i] != s[i]) {
            return false;
        }
    }
    return true;
}