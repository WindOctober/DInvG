
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
extern vector<Location*>* loclist;
extern vector<TransitionRelation*>* transList;
extern int getTransIndex(string name);
extern bool backtrack_flag;
extern C_Polyhedron* trivial;
extern int bang_count;
extern int single_pre_prune_bang_count;
extern int single_post_prune_bang_count;
extern int weave_count;
extern int single_weave_count;
extern Timer total_timer;
extern Timer collect_timer;
extern int total_time;
extern int collect_time;
extern int single_collect_time;
extern int backtrack_count;
extern int backtrack_success;
extern int merge_count;
extern int bang_count_in_merge;
extern Counter counter;
extern Timer single_merge_sub_sequences_timer;
extern void collect_invariants(C_Polyhedron& cpoly, C_Polyhedron& invd);
extern void collect_invariants_for_one_location_by_eliminating(
    int target_index,
    C_Polyhedron& cpoly,
    C_Polyhedron& invd);
extern void Clear_Location_Invariant();
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
void Tree::set_target_index(int index) {
    target_index = index;
}
void Tree::set_max_clump_count() {
    int max = -1;
    vector<Clump>::iterator vi;

    for (vi = clumps.begin(); vi < clumps.end(); vi++) {
        if (vi->size() > max) {
            max = vi->size();
        }
    }

    max_clump_count = max;
}

void Tree::Original_Prior(vector<Clump>& clumps) {
    // copy from "prior2"

    vector<int> relatedLocIndex;
    vector<int> unrelatedLocIndex;
    vector<int> relatedTransIndex;
    vector<int> unrelatedTransIndex;
    vector<int> targetIndex;

    string target = (*loclist)[target_index]->getName();
    int transition_index;
    string tr_preloc_name, tr_postloc_name;

    vector<Clump>::iterator vi;

    int index = 0;
    for (vi = clumps.begin(); vi < clumps.end(); vi++) {
        if (vi->get_category() == "Transition") {
            transition_index = getTransIndex(vi->getName());
            tr_preloc_name = (*transList)[transition_index]->getPreLocName();
            tr_postloc_name = (*transList)[transition_index]->getPostLocName();
            if (tr_preloc_name == target || tr_postloc_name == target) {
                relatedTransIndex.push_back(index);
            } else {
                unrelatedTransIndex.push_back(index);
            }
        } else if (vi->get_category() == "Location") {
            if (vi->getName() == target) {
                relatedLocIndex.push_back(index);
            } else {
                unrelatedLocIndex.push_back(index);
            }
        }
        index++;
    }

    set_ra(relatedLocIndex.size());
    set_er(relatedTransIndex.size());
    set_unra(unrelatedLocIndex.size());
    set_uner(unrelatedTransIndex.size());

    targetIndex.insert(targetIndex.end(), unrelatedLocIndex.begin(),
                       unrelatedLocIndex.end());
    targetIndex.insert(targetIndex.end(), unrelatedTransIndex.begin(),
                       unrelatedTransIndex.end());
    targetIndex.insert(targetIndex.end(), relatedTransIndex.begin(),
                       relatedTransIndex.end());
    targetIndex.insert(targetIndex.end(), relatedLocIndex.begin(),
                       relatedLocIndex.end());
    set_tree(clumps);
}

void Tree::Reorder_Target_Prior_1(vector<Clump>& clumps) {
    vector<int> first_index;
    vector<int> second_index;
    string target = (*loclist)[target_index]->getName();
    int transition_index;
    string tr_preloc_name, tr_postloc_name;
    int relatedLocIndex = 0, relatedTransIndex = 0, unrelatedLocIndex = 0,
        unrelatedTransIndex = 0;

    vector<Clump>::iterator vi;

    int j = 0;
    for (vi = clumps.begin(); vi < clumps.end(); vi++) {
        if (vi->get_category() == "Transition") {
            transition_index = getTransIndex(vi->getName());
            tr_preloc_name = (*transList)[transition_index]->getPreLocName();
            tr_postloc_name = (*transList)[transition_index]->getPostLocName();
            if (tr_preloc_name == target || tr_postloc_name == target) {
                first_index.push_back(j);
                relatedTransIndex++;
            } else {
                second_index.push_back(j);
                unrelatedTransIndex++;
            }
        } else if (vi->get_category() == "Location") {
            if (vi->getName() == target) {
                first_index.push_back(j);
                relatedLocIndex++;
            } else {
                second_index.push_back(j);
                unrelatedLocIndex++;
            }
        }
        j++;
    }

    set_ra(relatedLocIndex);
    set_er(relatedTransIndex);
    set_unra(unrelatedLocIndex);
    set_uner(unrelatedTransIndex);

    second_index.insert(second_index.end(), first_index.begin(),
                        first_index.end());

    vector<Clump> ordered_vcl;
    for (int i = 0; i < clumps.size(); i++) {
        ordered_vcl.push_back(clumps[second_index[i]]);
    }

    set_tree(ordered_vcl);
}

void Tree::Reorder_Target_Prior_2(vector<Clump>& clumps) {
    vector<int> relatedLocIndex;
    vector<int> unrelatedLocIndex;
    vector<int> relatedTransIndex;
    vector<int> unrelatedTransIndex;
    vector<int> targetIndex;

    string target = (*loclist)[target_index]->getName();
    int transition_index;
    string tr_preloc_name, tr_postloc_name;

    vector<Clump>::iterator vi;

    int j = 0;
    for (vi = clumps.begin(); vi < clumps.end(); vi++) {
        if (vi->get_category() == "Transition") {
            transition_index = getTransIndex(vi->getName());
            tr_preloc_name = (*transList)[transition_index]->getPreLocName();
            tr_postloc_name = (*transList)[transition_index]->getPostLocName();
            if (tr_preloc_name == target || tr_postloc_name == target) {
                relatedTransIndex.push_back(j);
            } else {
                unrelatedTransIndex.push_back(j);
            }
        } else if (vi->get_category() == "Location") {
            if (vi->getName() == target) {
                relatedLocIndex.push_back(j);
            } else {
                unrelatedLocIndex.push_back(j);
            }
        }
        j++;
    }

    set_ra(relatedLocIndex.size());
    set_er(relatedTransIndex.size());
    set_unra(unrelatedLocIndex.size());
    set_uner(unrelatedTransIndex.size());

    targetIndex.insert(targetIndex.end(), unrelatedLocIndex.begin(),
                       unrelatedLocIndex.end());
    targetIndex.insert(targetIndex.end(), unrelatedTransIndex.begin(),
                       unrelatedTransIndex.end());
    targetIndex.insert(targetIndex.end(), relatedTransIndex.begin(),
                       relatedTransIndex.end());
    targetIndex.insert(targetIndex.end(), relatedLocIndex.begin(),
                       relatedLocIndex.end());

    vector<Clump> ordered_vcl;
    for (int i = 0; i < clumps.size(); i++) {
        ordered_vcl.push_back(clumps[targetIndex[i]]);
    }

    set_tree(ordered_vcl);
}

void Tree::Reorder_Target_Prior_3(vector<Clump>& clumps) {
    vector<int> relatedLocIndex;
    vector<int> unrelatedLocIndex;
    vector<int> relatedTransIndex;
    vector<int> unrelatedTransIndex;
    vector<int> targetIndex;

    string target = (*loclist)[target_index]->getName();
    int transition_index;
    string tr_preloc_name, tr_postloc_name;

    vector<Clump>::iterator vi;

    int j = 0;
    for (vi = clumps.begin(); vi < clumps.end(); vi++) {
        if (vi->get_category() == "Transition") {
            transition_index = getTransIndex(vi->getName());
            tr_preloc_name = (*transList)[transition_index]->getPreLocName();
            tr_postloc_name = (*transList)[transition_index]->getPostLocName();
            if (tr_preloc_name == target || tr_postloc_name == target) {
                relatedTransIndex.push_back(j);
            } else {
                unrelatedTransIndex.push_back(j);
            }
        } else if (vi->get_category() == "Location") {
            if (vi->getName() == target) {
                relatedLocIndex.push_back(j);
            } else {
                unrelatedLocIndex.push_back(j);
            }
        }
        j++;
    }

    set_ra(relatedLocIndex.size());
    set_er(relatedTransIndex.size());
    set_unra(unrelatedLocIndex.size());
    set_uner(unrelatedTransIndex.size());

    // ***
    // reinter -> reintra -> unintra -> uninter
    // ***
    // depth min(i.e. 0)
    /*
    targetIndex.insert(targetIndex.end(),
    unrelatedTransIndex.begin(), unrelatedTransIndex.end());
    targetIndex.insert(targetIndex.end(),
    unrelatedLocIndex.begin(), unrelatedLocIndex.end());
    targetIndex.insert(targetIndex.end(),
    relatedLocIndex.begin(), relatedLocIndex.end());
    targetIndex.insert(targetIndex.end(),
    relatedTransIndex.begin(), relatedTransIndex.end());
    */
    // depth max

    // ***
    // reintra -> unintra -> reinter -> uninter
    // ***
    // depth min(i.e. 0)
    targetIndex.insert(targetIndex.end(), unrelatedTransIndex.begin(),
                       unrelatedTransIndex.end());
    targetIndex.insert(targetIndex.end(), relatedTransIndex.begin(),
                       relatedTransIndex.end());
    targetIndex.insert(targetIndex.end(), unrelatedLocIndex.begin(),
                       unrelatedLocIndex.end());
    targetIndex.insert(targetIndex.end(), relatedLocIndex.begin(),
                       relatedLocIndex.end());
    // depth max

    vector<Clump> ordered_vcl;
    for (int i = 0; i < clumps.size(); i++) {
        ordered_vcl.push_back(clumps[targetIndex[i]]);
    }

    set_tree(ordered_vcl);
}

void Tree::extract_vcl_for_one_location_about_intra(vector<Clump>& clumps) {
    vector<int> relatedLocIndex;
    vector<int> unrelatedLocIndex;
    vector<int> relatedTransIndex;
    vector<int> unrelatedTransIndex;
    vector<int> targetIndex;

    string target = (*loclist)[target_index]->getName();
    int transition_index;
    string tr_preloc_name, tr_postloc_name;

    vector<Clump>::iterator vi;

    int j = 0;
    for (vi = clumps.begin(); vi < clumps.end(); vi++) {
        if (vi->get_category() == "Transition") {
            transition_index = getTransIndex(vi->getName());
            tr_preloc_name = (*transList)[transition_index]->getPreLocName();
            tr_postloc_name = (*transList)[transition_index]->getPostLocName();
            if (tr_preloc_name == target || tr_postloc_name == target) {
                relatedTransIndex.push_back(j);
            } else {
                unrelatedTransIndex.push_back(j);
            }
        } else if (vi->get_category() == "Location") {
            if (vi->getName() == target) {
                relatedLocIndex.push_back(j);
            } else {
                unrelatedLocIndex.push_back(j);
            }
        }
        j++;
    }

    set_ra(relatedLocIndex.size());
    // set_er(relatedTransIndex.size());
    // set_unra(unrelatedLocIndex.size());
    // set_uner(unrelatedTransIndex.size());

    targetIndex.insert(targetIndex.end(), relatedLocIndex.begin(),
                       relatedLocIndex.end());
    vector<Clump> ordered_vcl;
    int rlid;
    if (targetIndex.size() == 1) {
        rlid = targetIndex[0];
    } else {
        cout << endl << "Error: There are more than one related location index";
        exit(-1);
    }
    ordered_vcl.push_back(clumps[rlid]);
    set_tree(ordered_vcl);
}

void Tree::Print_Prune_Tree(int depth, string weavedorbanged) {
    int dth;
    int clumpsNum = size();

    // cout<<endl;
    cout << endl
         << "( " << weavedorbanged << " Prune Tree, current length is "
         << clumpsNum - depth;
    if (weavedorbanged == "Banged") {
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
        for (int j = 0; j < get_clump(dth - 1).getCount(); j++) {
            if (j == get_clump(dth - 1).get_gli() && dth > depth) {
                cout << "[" << j << "]";
            } else {
                cout << " " << j << " ";
            }
        }
        cout << " --  " << get_clump(dth - 1).get_category();
        cout << ":: " << get_clump(dth - 1).getName();
    }
}

void Tree::Print_Prune_Tree(int depth, int hb, int lb, string weavedorbanged) {
    int dth;
    int clumpsNum = size();

    // cout<<endl;
    cout << endl
         << "( " << weavedorbanged << " Prune Tree, current length is "
         << hb + 1 - depth;
    if (weavedorbanged == "Banged") {
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
            if (get_clump(dth - 1).getCount() - 1 < j) {
                cout << "   ";
            } else if (lb <= dth - 1 && dth - 1 <= hb) {
                if (j == get_clump(dth - 1).get_gli() && dth > depth) {
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
        for (int j = 0; j < get_clump(dth-1).getCount(); j++){
            if (lb <= dth-1 && dth-1 <= hb){
                if (j == get_clump(dth-1).get_gli() && dth > depth){
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
        cout << " --  " << get_clump(dth - 1).get_category();
        if (get_clump(dth - 1).get_category() == "Location") {
            cout << "_Intra";
        } else if (get_clump(dth - 1).get_category() == "Transition") {
            cout << "_Inter";
        } else {
            cout << "Neither Location nor Transition!!!";
        }
        cout << ":: " << get_clump(dth - 1).getName();
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
    if (weavedorbanged == "Banged") {
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
            if (get_clump(dth - 1).getCount() - 1 < j) {
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
        cout << " --  " << get_clump(dth - 1).get_category();
        cout << ":: " << get_clump(dth - 1).getName();
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
    if (weavedorbanged == "Banged") {
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
        for (int j = 0; j < get_clump(dth - 1).getCount(); j++) {
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
        cout << " --  " << get_clump(dth - 1).get_category();
        cout << ":: " << get_clump(dth - 1).getName();
        if (lb <= dth - 1 && dth - 1 <= hb) {
            i++;
        }
    }
}

void Tree::prune_node_self_inspection(int target_index, C_Polyhedron& invd) {
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
        (*vi).clear();
        cout << endl
             << "depth: " << dth
             << ", clear_lower_gli, gli : " << (*vi).get_gli() << " "
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
        clumps_gli.push_back((*vi).get_gli());
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
                              target_index * (dimension + 1));
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
            (*vk).extract_invariant_for_one_location_by_eliminating(
                cl.getReference(i).minimized_constraints());

            cout << endl << "to update constraints";
            (*vk).update_dual_constraints(clumps_poly);
        }
        cout << endl << "dth: " << dth << ", " << (*vk).getName();
        cout << endl << "this union of clumps poly: " << clumps_poly;
        dth--;
    }
    for (vk = tr_union.end() - 1; vk >= tr_union.begin(); vk--) {
        cout << (*vk);
    }

    // take each "gli" from polys[gli] and test inclusion for polys[gli] and
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
        cout << endl
             << "This PRE_LOC has banged:" << single_pre_prune_bang_count;
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
        cout << endl
             << "This PRE_LOC has banged:" << single_pre_prune_bang_count;
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
        cout << endl
             << "This PRE_LOC has banged:" << single_pre_prune_bang_count;
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
        cout << endl
             << "This PRE_LOC has banged:" << single_pre_prune_bang_count;
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
        cout << endl
             << "This PRE_LOC has banged:" << single_pre_prune_bang_count;
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
        cout << endl
             << "This PRE_LOC has banged:" << single_pre_prune_bang_count;
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
        cout << endl
             << "This PRE_LOC has banged:" << single_pre_prune_bang_count;
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
        cout << endl
             << "This PRE_LOC has banged:" << single_pre_prune_bang_count;
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
    int target_index = clumpsNum - (ra + er) - 1;

    if (sequences.size() > 2) {
        vector<vector<vector<int>>>::iterator it;
        int hb = clumps.size() - 1;
        int lb = clumps.size();
        for (it = sequences.begin();
             hb > target_index && it < sequences.end() - 1; it = it + 2) {
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
        // for (it=sequences.begin(); hb>target_index && it<sequences.end()-1;
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
    // int target_index = clumpsNum-(ra+er)-1;

    if (sequences.size() > 2) {
        vector<vector<vector<int>>>::iterator it;

        for (it = sequences.begin(); it < sequences.end() - 2; it = it + 1) {
            merged_sequences.push_back(*it);
        }

        int hb = 0 - 1;
        int lb = 0;
        // for (it=sequences.begin(); hb>target_index && it<sequences.end()-1;
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
        single_merge_sub_sequences_timer.compute_time_elapsed();

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
                            C_Polyhedron& cpoly,
                            Clump& invd_vp,
                            int hb,
                            int lb) {
    if (i == two_sub_sequences.size() - 1) {
        // cout<<endl;
        // cout<<endl<<"/-----------------------------";
        // Print_Prune_Sequence_Tree(sequence, lb, hb, lb,"Weaved");
        collect_timer.restart();
        // collect_invariant_polys(cpoly, invd_vp);
        // merged_sub_sequences.push_back(sequence);
        collect_invariant_polys_and_sub_sequences(invd_vp, merged_sub_sequences,
                                                  cpoly, sequence);
        collect_timer.stop();
        cout << endl
             << "- The collect_invariant_polys_and_sub_sequences Time Taken "
                "(0.01s) = "
             << collect_timer.compute_time_elapsed();
        // cout<<endl<<"\\-----------------------------"<<endl;
        return;
    }

    int j = 0;
    vector<int> banged_s;
    bool s_banged_flag = false;
    while (j < two_sub_sequences[i + 1].size()) {
        vector<int> s;
        s.insert(s.end(), two_sub_sequences[i + 1][j].begin(),
                 two_sub_sequences[i + 1][j].end());

        if (banged_s.size() > 0 &&
            has_the_same_sequences_from_the_left(banged_s, s)) {
            j++;
            continue;
        } else {
            banged_s.clear();
            s_banged_flag = false;
        }

        C_Polyhedron p(cpoly);
        int index = 0;
        vector<int> temp_s;
        vector<int> read_s = sequence;

        for (vector<int>::iterator it = s.begin(); it < s.end(); it++) {
            temp_s.push_back(*it);
            read_s.push_back(*it);
            p.intersection_assign(get_clump(depth - index).getReference(*it));
            if (invd_vp.contains(p)) {
                // Print_Prune_Sequence_Tree(read_s, depth-index, hb, lb,
                // "Banged");
                bang_count++;
                single_pre_prune_bang_count++;
                bang_count_in_merge++;

                banged_s = temp_s;
                s_banged_flag = true;
                break;
            }
            index++;
        }

        if (s_banged_flag != true) {
            Merge_recursive2(two_sub_sequences, merged_sub_sequences, read_s,
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
    C_Polyhedron& cpoly,
    Clump& invd_vp) {
    if (total_timer.compute_time_elapsed() >= total_time) {
        cout << endl << "Time is up!";
        return;
    }

    if (invd_vp.contains(cpoly)) {
        bang_count++;
        single_pre_prune_bang_count++;
        counter.set_pre_pbc_at_location_and_depth(get_target_index(), depth);
        if (print_tree) {
            Print_Prune_Tree(
                depth, hb, lb,
                "Banged");
        }
        return;
    }

    if (depth == lb) {
        if (print_tree) {
            Print_Prune_Tree(depth, hb, lb, "Weaved");
        }
        collect_timer.restart();
        collect_invariant_polys_and_sub_sequences(invd_vp, sub_sequences, cpoly,
                                                  hb, lb);
        collect_timer.stop();

        return;
    }

    get_clump(depth - 1).clear();
    while (get_clump(depth - 1).has_next()) {
        // cout<<endl<<"in while...next()";
        // cout<<endl<<"depth:"<<depth<<", cpoly:";
        // cout<<endl<<cpoly;
        C_Polyhedron p(cpoly);
        p.intersection_assign(get_clump(depth - 1).getReference());
        dfs_sub_sequences_traverse_recursive(sub_sequences, hb, lb, depth - 1,
                                             p, invd_vp);
        if (backtrack_flag == true) {
            if (invd_vp.contains(cpoly)) {
                backtrack_success++;
                cout << endl << "Pruned by backtracking in depth " << depth;
                get_clump(depth - 1).clear();
                return;
            } else {
                if (backtrack_success >= 1) {
                    backtrack_count++;
                    backtrack_success = 0;
                }
                backtrack_flag = false;
            }
        }
        get_clump(depth - 1).next();
    }

    // cout<<endl<<"< < < Tree::dfs_sub_sequences_traverse_recursive()";
    return;
}

void Tree::collect_invariant_polys(C_Polyhedron& cpoly, Clump& invd_vp) {
    invd_vp.insert(cpoly);
    cout << endl << "  invd_vp.size():" << invd_vp.getCount();
}

void Tree::collect_sub_sequences(vector<vector<int>>& sub_sequences,
                                 int hb,
                                 int lb) {
    // cout<<endl<<"> > > Tree::collect_sub_sequences()";

    vector<int> s;
    int dth;
    for (dth = hb; dth >= lb; dth--) {
        s.push_back(get_clump(dth).get_gli());
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
    C_Polyhedron& cpoly,
    int hb,
    int lb) {
    // cout<<endl<<"> > > Tree::collect_invariant_polys_and_sub_sequences()";
    vector<int> s;
    int dth;
    for (dth = hb; dth >= lb; dth--) {
        s.push_back(get_clump(dth).get_gli());
    }
    //  collect invd_vp
    vector<int> erase_index;
    erase_index = invd_vp.insert_with_erase_index(cpoly);
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
    C_Polyhedron& cpoly,
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
    erase_index = invd_vp.insert_with_erase_index(cpoly);
    cout << endl << "  invd_vp.size():" << invd_vp.getCount();

    //  add above collectors
    vector<int>::reverse_iterator vi;
    for (vi = erase_index.rbegin(); vi < erase_index.rend(); vi++) {
        sub_sequences.erase(sub_sequences.begin() + (*vi));
    }
    sub_sequences.push_back(sequence);

    return;
}

void Tree::dfs_sequences_traverse(vector<vector<vector<int>>> sequences,
                                  C_Polyhedron& initp,
                                  C_Polyhedron& invd) {
    cout << endl << "> > > Tree::dfs_sequences_traverse()";

    int start = -1;
    vector<int> sequence;
    int depth = clumps.size() - 1;
    dfs_sequences_traverse_recursive2(sequence, sequences, start, depth, initp,
                                      invd);

    cout << endl << "< < < Tree::dfs_sequences_traverse()";
}

void Tree::dfs_sequences_traverse_recursive2(
    vector<int>& sequence,
    vector<vector<vector<int>>> sequences,
    int i,
    int depth,
    C_Polyhedron& cpoly,
    C_Polyhedron& invd) {
    if (total_timer.compute_time_elapsed() >= total_time) {
        cout << endl << "Time is up!";
        return;
    }

    if (i == sequences.size() - 1) {
        weave_count++;
        single_weave_count++;

        cout << endl;
        cout << endl << "sequence:";
        for (int k = 0; k < sequence.size(); k++) {
            cout << sequence[k];
        }
        cout << endl << "/-----------------------------";
        if (print_tree) {
            Print_Prune_Sequence_Tree(sequence, 0, "Weaved");
        }
        collect_timer.restart();
        collect_invariants_for_one_location_by_eliminating(target_index, cpoly,
                                                           invd);
        cout << endl;
        cout << endl << "- Have Collected " << weave_count << " invariant(s)";
        collect_timer.stop();
        cout << endl
             << "- The collect_invariants Time Taken (0.01s) = "
             << collect_timer.compute_time_elapsed();
        collect_time = collect_time + collect_timer.compute_time_elapsed();
        single_collect_time =
            single_collect_time + collect_timer.compute_time_elapsed();
        cout << endl << "------------------------------";
        cout << endl << "- cpoly: " << endl << "  " << cpoly;
        cout << endl << "- invd: " << endl << "  " << invd;
        cout << endl
             << "- invariant: " << endl
             << "  " << (*loclist)[target_index]->GetInv();
        cout << endl << "\\-----------------------------";
        return;
    }

    int j = 0;
    vector<int> banged_s;
    bool s_banged_flag = false;
    while (j < sequences[i + 1].size()) {
        vector<int> s;
        s.insert(s.end(), sequences[i + 1][j].begin(),
                 sequences[i + 1][j].end());

        if (banged_s.size() > 0 &&
            has_the_same_sequences_from_the_left(banged_s, s)) {
            j++;
            continue;
        } else {
            banged_s.clear();
            s_banged_flag = false;
        }

        C_Polyhedron p(cpoly);
        int index = 0;
        vector<int> temp_s;
        vector<int> read_s = sequence;

        for (vector<int>::iterator it = s.begin(); it < s.end(); it++) {
            temp_s.push_back(*it);
            read_s.push_back(*it);
            p.intersection_assign(get_clump(depth - index).getReference(*it));
            if (invd.contains(p)) {
                bang_count++;
                single_post_prune_bang_count++;
                counter.set_pst_pbc_at_location_and_depth(get_target_index(),
                                                          depth - index);

                // cout<<endl;
                // cout<<endl<<"sequence:";
                for (int k = 0; k < read_s.size(); k++) {
                    // cout<<read_s[k];
                }
                if (print_tree) {
                    Print_Prune_Sequence_Tree(read_s, depth - index, "Banged");
                }
                banged_s = temp_s;
                s_banged_flag = true;
                break;
            }
            index++;
        }

        if (s_banged_flag != true) {
            dfs_sequences_traverse_recursive2(read_s, sequences, i + 1,
                                              depth - index, p, invd);
        }
        j++;
    }
    return;
}

bool Tree::has_the_same_sequences_from_the_left(vector<int> banged_s,
                                                vector<int> s) {
    for (int i = 0; i < banged_s.size(); i++) {
        if (banged_s[i] != s[i]) {
            return false;
        }
    }
    return true;
}