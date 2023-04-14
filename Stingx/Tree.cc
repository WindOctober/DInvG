
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
extern var_info * f, *fd, *fm;
extern vector<Location *> * loclist;
extern vector<TransitionRelation *> * trlist;
extern int get_index_of_transition(string name);
extern bool backtrack_flag;
extern C_Polyhedron *trivial;
extern int debug;
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
extern void collect_invariants(C_Polyhedron & cpoly, C_Polyhedron & invd);
extern void collect_invariants_for_one_location_by_eliminating(int target_index, C_Polyhedron & cpoly, C_Polyhedron & invd);
extern void Clear_Location_Invariant();
extern void Print_Location();
extern bool print_tree;

void Tree::initialize(vector<Clump> & outer_vcl){
    this->vcl = outer_vcl;
}

Tree::Tree(){
    ;
}

Tree::Tree(vector<Clump> & outer_vcl){
    initialize(outer_vcl);
}

void Tree::set_tree(vector<Clump> & outer_vcl){
    initialize(outer_vcl);
}

void Tree::set_ra(int amount){ra = amount;}
void Tree::set_er(int amount){er = amount;}
void Tree::set_unra(int amount){unra = amount;}
void Tree::set_uner(int amount){uner = amount;}
void Tree::set_target_index(int index){
    target_index = index;
}
void Tree::set_max_clump_count(){
    int max=-1;
    vector<Clump>::iterator vi;

    for (vi = vcl.begin(); vi < vcl.end(); vi++){
        if (vi->size() > max){
            max = vi->size();
        }
    }

    max_clump_count = max;
}

void Tree::Original_Prior(vector<Clump> &outer_vcl){
    // copy from "prior2"
    
    vector<int> related_location_index;
    vector<int> unrelated_location_index;
    vector<int> related_transition_index;
    vector<int> unrelated_transition_index;
    vector<int> target_prior_index;

    string target = (*loclist)[target_index]->get_name();
    int transition_index;
    string tr_preloc_name, tr_postloc_name;

    vector<Clump>::iterator vi;

    int j=0;
    for (vi = outer_vcl.begin(); vi < outer_vcl.end(); vi++){
        if ( vi->get_category() == "Transition"){
            transition_index = get_index_of_transition(vi->get_name());
            tr_preloc_name = (*trlist)[transition_index]->get_preloc_name();
            tr_postloc_name = (*trlist)[transition_index]->get_postloc_name();
            if ( tr_preloc_name == target || tr_postloc_name == target ){
                related_transition_index.push_back(j);
            }
            else {
                unrelated_transition_index.push_back(j);
            }
        }
        else if ( vi->get_category() == "Location"){
            if ( vi->get_name() == target ){
                related_location_index.push_back(j);
            }
            else {
                unrelated_location_index.push_back(j);
            }
        }
        j++;
    }

    set_ra(related_location_index.size());
    set_er(related_transition_index.size());
    set_unra(unrelated_location_index.size());
    set_uner(unrelated_transition_index.size());

    target_prior_index.insert(target_prior_index.end(), unrelated_location_index.begin(), unrelated_location_index.end());
    target_prior_index.insert(target_prior_index.end(), unrelated_transition_index.begin(), unrelated_transition_index.end());
    target_prior_index.insert(target_prior_index.end(), related_transition_index.begin(), related_transition_index.end());
    target_prior_index.insert(target_prior_index.end(), related_location_index.begin(), related_location_index.end());

    vector<Clump> ordered_vcl;
    for (int i = 0; i < outer_vcl.size(); i++){
        ordered_vcl.push_back(outer_vcl[target_prior_index[i]]);
    }

    // modify reason: outer_vcl is original vcl
    //set_tree(ordered_vcl);
    set_tree(outer_vcl);
}

void Tree::Reorder_Target_Prior_1(vector<Clump> &outer_vcl){
    vector<int> first_index;
    vector<int> second_index;
    string target = (*loclist)[target_index]->get_name();
    int transition_index;
    string tr_preloc_name, tr_postloc_name;
    int related_location_index=0, related_transition_index=0, unrelated_location_index=0, unrelated_transition_index=0;

    vector<Clump>::iterator vi;

    int j=0;
    for (vi = outer_vcl.begin(); vi < outer_vcl.end(); vi++){
        if ( vi->get_category() == "Transition"){
            transition_index = get_index_of_transition(vi->get_name());
            tr_preloc_name = (*trlist)[transition_index]->get_preloc_name();
            tr_postloc_name = (*trlist)[transition_index]->get_postloc_name();
            if ( tr_preloc_name == target || tr_postloc_name == target ){
                first_index.push_back(j);
                related_transition_index++;
            }
            else {
                second_index.push_back(j);
                unrelated_transition_index++;
            }
        }
        else if ( vi->get_category() == "Location"){
            if ( vi->get_name() == target ){
                first_index.push_back(j);
                related_location_index++;
            }
            else {
                second_index.push_back(j);
                unrelated_location_index++;
            }
        }
        j++;
    }

    set_ra(related_location_index);
    set_er(related_transition_index);
    set_unra(unrelated_location_index);
    set_uner(unrelated_transition_index);

    second_index.insert(second_index.end(), first_index.begin(), first_index.end());

    vector<Clump> ordered_vcl;
    for (int i = 0; i < outer_vcl.size(); i++){
        ordered_vcl.push_back(outer_vcl[second_index[i]]);
    }

    set_tree(ordered_vcl);

}

void Tree::Reorder_Target_Prior_2(vector<Clump> &outer_vcl){

    vector<int> related_location_index;
    vector<int> unrelated_location_index;
    vector<int> related_transition_index;
    vector<int> unrelated_transition_index;
    vector<int> target_prior_index;

    string target = (*loclist)[target_index]->get_name();
    int transition_index;
    string tr_preloc_name, tr_postloc_name;

    vector<Clump>::iterator vi;

    int j=0;
    for (vi = outer_vcl.begin(); vi < outer_vcl.end(); vi++){
        if ( vi->get_category() == "Transition"){
            transition_index = get_index_of_transition(vi->get_name());
            tr_preloc_name = (*trlist)[transition_index]->get_preloc_name();
            tr_postloc_name = (*trlist)[transition_index]->get_postloc_name();
            if ( tr_preloc_name == target || tr_postloc_name == target ){
                related_transition_index.push_back(j);
            }
            else {
                unrelated_transition_index.push_back(j);
            }
        }
        else if ( vi->get_category() == "Location"){
            if ( vi->get_name() == target ){
                related_location_index.push_back(j);
            }
            else {
                unrelated_location_index.push_back(j);
            }
        }
        j++;
    }

    set_ra(related_location_index.size());
    set_er(related_transition_index.size());
    set_unra(unrelated_location_index.size());
    set_uner(unrelated_transition_index.size());

    target_prior_index.insert(target_prior_index.end(), unrelated_location_index.begin(), unrelated_location_index.end());
    target_prior_index.insert(target_prior_index.end(), unrelated_transition_index.begin(), unrelated_transition_index.end());
    target_prior_index.insert(target_prior_index.end(), related_transition_index.begin(), related_transition_index.end());
    target_prior_index.insert(target_prior_index.end(), related_location_index.begin(), related_location_index.end());

    vector<Clump> ordered_vcl;
    for (int i = 0; i < outer_vcl.size(); i++){
        ordered_vcl.push_back(outer_vcl[target_prior_index[i]]);
    }

    set_tree(ordered_vcl);

}

void Tree::Reorder_Target_Prior_3(vector<Clump> &outer_vcl){
    vector<int> related_location_index;
    vector<int> unrelated_location_index;
    vector<int> related_transition_index;
    vector<int> unrelated_transition_index;
    vector<int> target_prior_index;

    string target = (*loclist)[target_index]->get_name();
    int transition_index;
    string tr_preloc_name, tr_postloc_name;

    vector<Clump>::iterator vi;

    int j=0;
    for (vi = outer_vcl.begin(); vi < outer_vcl.end(); vi++){
        if ( vi->get_category() == "Transition"){
            transition_index = get_index_of_transition(vi->get_name());
            tr_preloc_name = (*trlist)[transition_index]->get_preloc_name();
            tr_postloc_name = (*trlist)[transition_index]->get_postloc_name();
            if ( tr_preloc_name == target || tr_postloc_name == target ){
                related_transition_index.push_back(j);
            }
            else {
                unrelated_transition_index.push_back(j);
            }
        }
        else if ( vi->get_category() == "Location"){
            if ( vi->get_name() == target ){
                related_location_index.push_back(j);
            }
            else {
                unrelated_location_index.push_back(j);
            }
        }
        j++;
    }

    set_ra(related_location_index.size());
    set_er(related_transition_index.size());
    set_unra(unrelated_location_index.size());
    set_uner(unrelated_transition_index.size());

    // ***
    // reinter -> reintra -> unintra -> uninter
    // ***
    //depth min(i.e. 0)
    /*
    target_prior_index.insert(target_prior_index.end(), unrelated_transition_index.begin(), unrelated_transition_index.end());
    target_prior_index.insert(target_prior_index.end(), unrelated_location_index.begin(), unrelated_location_index.end());
    target_prior_index.insert(target_prior_index.end(), related_location_index.begin(), related_location_index.end());
    target_prior_index.insert(target_prior_index.end(), related_transition_index.begin(), related_transition_index.end());
    */
    //depth max

    // ***
    // reintra -> unintra -> reinter -> uninter
    // ***
    //depth min(i.e. 0)
    target_prior_index.insert(target_prior_index.end(), unrelated_transition_index.begin(), unrelated_transition_index.end());
    target_prior_index.insert(target_prior_index.end(), related_transition_index.begin(), related_transition_index.end());
    target_prior_index.insert(target_prior_index.end(), unrelated_location_index.begin(), unrelated_location_index.end());
    target_prior_index.insert(target_prior_index.end(), related_location_index.begin(), related_location_index.end());
    //depth max

    vector<Clump> ordered_vcl;
    for (int i = 0; i < outer_vcl.size(); i++){
        ordered_vcl.push_back(outer_vcl[target_prior_index[i]]);
    }

    set_tree(ordered_vcl);

}

void Tree::extract_vcl_for_one_location_about_intra(vector<Clump> &outer_vcl){
    vector<int> related_location_index;
    vector<int> unrelated_location_index;
    vector<int> related_transition_index;
    vector<int> unrelated_transition_index;
    vector<int> target_prior_index;

    string target = (*loclist)[target_index]->get_name();
    int transition_index;
    string tr_preloc_name, tr_postloc_name;

    vector<Clump>::iterator vi;

    int j=0;
    for (vi = outer_vcl.begin(); vi < outer_vcl.end(); vi++){
        if ( vi->get_category() == "Transition"){
            transition_index = get_index_of_transition(vi->get_name());
            tr_preloc_name = (*trlist)[transition_index]->get_preloc_name();
            tr_postloc_name = (*trlist)[transition_index]->get_postloc_name();
            if ( tr_preloc_name == target || tr_postloc_name == target ){
                related_transition_index.push_back(j);
            }
            else {
                unrelated_transition_index.push_back(j);
            }
        }
        else if ( vi->get_category() == "Location"){
            if ( vi->get_name() == target ){
                related_location_index.push_back(j);
            }
            else {
                unrelated_location_index.push_back(j);
            }
        }
        j++;
    }

    set_ra(related_location_index.size());
    set_er(related_transition_index.size());
    set_unra(unrelated_location_index.size());
    set_uner(unrelated_transition_index.size());

    target_prior_index.insert(target_prior_index.end(), related_location_index.begin(), related_location_index.end());

    vector<Clump> ordered_vcl;
    int rlid;
    if(target_prior_index.size()==1){
        rlid = target_prior_index[0];
    }
    else{
        tcout<<endl<<"Error: There are more than one related location index";
    }
    ordered_vcl.push_back(outer_vcl[rlid]);

    set_tree(ordered_vcl);
}

void Tree::Print_Prune_Tree(int depth, string weavedorbanged){

    int dth;
    int ncl = size();

    //tcout<<endl;
    tcout<<endl<<"( "<<weavedorbanged<<" Prune Tree, current length is "<<ncl-depth;
    if (weavedorbanged == "Banged"){
        tcout<<endl<<"( in ";
        if (ncl-depth > get_ra()+get_er()){
            tcout<<"unrelated transition";
        }
        else {
            tcout<<"related transition";
        }
    }

    for (dth = ncl; dth > 0; dth--){
        tcout<<endl<<"( ";autoprint(ncl-1,dth-1);tcout<<"  ⋁  ";
        for (int j = 0; j < get_clump(dth-1).get_count(); j++){
            if (j == get_clump(dth-1).get_gli() && dth > depth){
                tcout<<"["<<j<<"]";
            }
            else {
                tcout<<" "<<j<<" ";
            }
        }
        tcout<<" --  "<<get_clump(dth-1).get_category();
        tcout<<":: "<<get_clump(dth-1).get_name();
    }

}

void Tree::Print_Prune_Tree(int depth, int hb, int lb, string weavedorbanged){

    int dth;
    int ncl = size();

    //tcout<<endl;
    tcout<<endl<<"( "<<weavedorbanged<<" Prune Tree, current length is "<<hb+1-depth;
    if (weavedorbanged == "Banged"){
        tcout<<endl<<"( in ";
        if (ncl-depth > get_ra()+get_er()){
            tcout<<"unrelated transition";
        }
        else {
            tcout<<"related transition";
        }
    }

    for (dth = ncl; dth > 0; dth--){
        tcout<<endl<<"( ";autoprint(ncl-1,dth-1);tcout<<"  ⋁  ";

        for (int j = 0; j < get_max_clump_count(); j++){
            if (get_clump(dth-1).get_count()-1 < j){
                tcout<<"   ";
            }
            else if (lb <= dth-1 && dth-1 <= hb){
                if (j == get_clump(dth-1).get_gli() && dth > depth){
                    tcout<<"["<<j<<"]";
                }
                else {
                    tcout<<" "<<j<<" ";
                }
            }
            else {
                tcout<<" "<<j<<" ";
            }
        }
        /*
        // old version, without smart blank with print Prune Tree
        for (int j = 0; j < get_clump(dth-1).get_count(); j++){
            if (lb <= dth-1 && dth-1 <= hb){
                if (j == get_clump(dth-1).get_gli() && dth > depth){
                    tcout<<"["<<j<<"]";
                }
                else {
                    tcout<<" "<<j<<" ";
                }
            }
            else {
                tcout<<" "<<j<<" ";
            }
        }
        */
        tcout<<" --  b: "<<counter.get_pre_pbc_about_location_and_depth(get_target_index(), dth-1);
        tcout<<" --  "<<get_clump(dth-1).get_category();
        if(get_clump(dth-1).get_category() == "Location"){
            tcout<<"_Intra";
        }
        else if(get_clump(dth-1).get_category() == "Transition"){
            tcout<<"_Inter";
        }
        else{
            tcout<<"Neither Location nor Transition!!!";
        }
        tcout<<":: "<<get_clump(dth-1).get_name();
    }

}

void Tree::Print_Prune_Sequence_Tree(vector<int> sequence, int depth, string weavedorbanged){

    int dth, i;
    int ncl = size();

    //tcout<<endl;
    tcout<<endl<<"( "<<weavedorbanged<<" Prune Tree, current length is "<<ncl-depth;
    if (weavedorbanged == "Banged"){
        tcout<<endl<<"( in ";
        if (ncl-depth > get_ra()+get_er()){
            tcout<<"unrelated transition";
        }
        else {
            tcout<<"related transition";
        }
    }

    i = 0;
    for (dth = ncl; dth > 0; dth--){
        tcout<<endl<<"( ";autoprint(ncl-1,dth-1);tcout<<"  ⋁  ";

        for (int j = 0; j < get_max_clump_count(); j++){
            if (get_clump(dth-1).get_count()-1 < j){
                tcout<<"   ";
            }
            else if (j == sequence[i] && dth > depth){
                tcout<<"["<<j<<"]";
            }
            else {
                tcout<<" "<<j<<" ";
            }
        }
        /*
        // old version, without smart blank with print Prune Tree
        for (int j = 0; j < get_clump(dth-1).get_count(); j++){
            if (j == sequence[i] && dth > depth){
                tcout<<"["<<j<<"]";
            }
            else {
                tcout<<" "<<j<<" ";
            }
        }
        */
        tcout<<" --  b: "<<counter.get_pst_pbc_about_location_and_depth(get_target_index(), dth-1);
        tcout<<" --  "<<get_clump(dth-1).get_category();
        tcout<<":: "<<get_clump(dth-1).get_name();
        i++;
    }

}

void Tree::Print_Prune_Sequence_Tree(vector<int> sequence, int depth, int hb, int lb, string weavedorbanged){

    int dth, i;
    int ncl = size();

    //tcout<<endl;
    tcout<<endl<<"( "<<weavedorbanged<<" Prune Tree, current length is "<<hb+1-depth;
    if (weavedorbanged == "Banged"){
        tcout<<endl<<"( in ";
        if (ncl-depth > get_ra()+get_er()){
            tcout<<"unrelated transition";
        }
        else {
            tcout<<"related transition";
        }
    }

    i = 0;
    for (dth = ncl; dth > 0; dth--){
        tcout<<endl<<"( ";autoprint(ncl-1,dth-1);tcout<<"  ⋁  ";
        for (int j = 0; j < get_clump(dth-1).get_count(); j++){
            if (lb <= dth-1 && dth-1 <= hb){
                if (j == sequence[i] && dth > depth){
                    tcout<<"["<<j<<"]";
                }
                else {
                    tcout<<" "<<j<<" ";
                }
            }
            else {
                tcout<<" "<<j<<" ";
            }
        }
        tcout<<" --  "<<get_clump(dth-1).get_category();
        tcout<<":: "<<get_clump(dth-1).get_name();
        if (lb <= dth-1 && dth-1 <= hb){
            i++;
        }
    }

}

void Tree::prune_node_self_inspection(int target_index, C_Polyhedron & invd){
   
    int dth = size()-1;
    vector<Clump>::iterator vi;
    
    store_clumps_gli();
    clear_pruned_node();
    //for (; dth>=0/*vcl.size()-ra-er*/; dth--){
        vi = vcl.begin() + dth;
        //vector<int> node_gli = (*vi).prune_all(invd);
        vector<int> node_gli = (*vi).prune_target(invd,clumps_gli[dth]);
        if (node_gli.size()){
            insert_pruned_node(dth,node_gli);
            backtrack_flag = false;
        }
    //}
    store_conflict_node();
    dth = first_conflict;
    while(dth-->0){
        vi = vcl.begin() + dth;
        (*vi).clear();
        tcout<<endl<<"depth: "<<dth<<", clear_lower_gli, gli : "<<(*vi).get_gli()<<" "<<(*vi).get_category()<<"::"<<(*vi).get_name();
    }

}

void Tree::insert_pruned_node(int depth, vector<int> node_gli){
    pruned_node.emplace_back(depth, node_gli);
}

void Tree::store_conflict_node(){
    vector<pair<int,vector<int>> >::iterator vi;
    vector<int> node_gli;
    vector<int>::iterator it;
    //vector<int> new_conflict_depth;
    int depth;

    conflict_depth.clear();
    for (vi=pruned_node.begin(); vi<pruned_node.end(); vi++){
        depth = (*vi).first;
        node_gli = (*vi).second;

        it = find(node_gli.begin(), node_gli.end(), clumps_gli[depth]);
        if (it != node_gli.end()){
            conflict_depth.push_back(depth);
        }
    }
    //conflict_depth = new_conflict_depth;
    if (conflict_depth.size() != 0){
        first_conflict = *conflict_depth.begin();
    }
    else {
        first_conflict = -1;
    }

    return;
}

void Tree::store_clumps_gli(){
    int dth;
    vector<Clump>::iterator vi;
    //vector<int> new_clumps_gli;
    clumps_gli.clear();
    for (dth = 0; dth < size(); dth++){
        vi = vcl.begin() + dth;
        clumps_gli.push_back((*vi).get_gli());
    }
    //clumps_gli = new_clumps_gli;
}

void Tree::prune_clumps_by_hierarchy_inclusion(){
    tcout<<endl;
    tcout<<endl<<"> > > prune_clumps_by_hierarchy_inclusion()";
    vector<Clump>::iterator vi;
    vector<C_Polyhedron>::iterator vj;
    vector<Location> tr_union;
    vector<Location>::iterator vk;

    // initialize union
    for (vi=vcl.begin(); vi<vcl.end(); vi++){
        Location clumps_union(dimension,f,fd,fm,"union_"+(*vi).get_name(),target_index*(dimension+1));
        tr_union.push_back(clumps_union);
    }
    for (vk=tr_union.end()-1; vk>=tr_union.begin(); vk--){
        tcout<<(*vk);
    }

    // build up union for each hierarchy
    int dth=tr_union.size()-1;
    while (dth>=0){
        vk=tr_union.begin()+dth;
        Clump cl=vcl[dth];
        C_Polyhedron clumps_poly(fd->get_dimension(), UNIVERSE);
        int i=0;
        for (i=0; i<cl.get_count(); i++){
            tcout<<endl<<"to extract invariant";
            (*vk).extract_invariant_for_one_location_by_eliminating(cl.get_reference(i).minimized_constraints());

            tcout<<endl<<"to update constraints";
            (*vk).update_dual_constraints(clumps_poly);
        }
        tcout<<endl<<"dth: "<<dth<<", "<<(*vk).get_name();
        tcout<<endl<<"this union of clumps poly: "<<clumps_poly;
        dth--;
    }
    for (vk=tr_union.end()-1; vk>=tr_union.begin(); vk--){
        tcout<<(*vk);
    }

    // take each "gli" from vp[gli] and test inclusion for vp[gli] and other hierarchy union 

    tcout<<endl<<"< < < prune_clumps_by_hierarchy inclusion()";
}

vector<vector<vector<int>>> Tree::sequences_generation(string divide_into_sections, C_Polyhedron & initp){
    tcout<<endl<<"> > > Tree::sequences generation()";

    vector<vector<vector<int>>> sequences;

    if (divide_into_sections == "divide_by_target_relation_based_on_StInG"){
        sequences = divide_by_target_relation_based_on_StInG(initp);
    }
    else if (divide_into_sections == "no_divide_for_test"){
        sequences = no_divide_for_test(initp);
    }
    else if (divide_into_sections == "divide_by_target_relation"){
        sequences = divide_by_target_relation(initp);
    }
    else if (divide_into_sections == "one_per_group"){
        sequences = one_per_group(initp);
    }
    else if (divide_into_sections == "two_per_group"){
        sequences = two_per_group(initp);
    }
    else if (divide_into_sections == "three_per_group"){
        sequences = three_per_group(initp);
    }
    else if (divide_into_sections == "four_per_group"){
        sequences = four_per_group(initp);
    }
    else if (divide_into_sections == "divide_target_into_double"){
        sequences = divide_target_into_double(initp);
    }
    else if (divide_into_sections == "divide_by_inter_transition"){
        sequences = divide_by_inter_transition(initp);
    }
    else if (divide_into_sections == "divide_prior2_into_four"){
        sequences = divide_prior2_into_four(initp);
    }
    else {
        tcout<<endl<<"divide_into_sections: wrong type";
    }

    //  Merge, especially like as "two_per_group"
    //sequences = merge_sub_sequences(sequences,initp);
    //sequences = merge_sub_sequences(sequences,initp);
    //sequences = merge_sub_sequences(sequences,initp);

    // Merge target location
    //sequences = merge_target_sub_sequences(sequences,initp);
    //sequences = merge_target_sub_sequences(sequences,initp);
    //sequences = merge_target_sub_sequences(sequences,initp);

    // Merge first two sub_sequences
    //sequences = merge_first_sub_sequences(sequences, initp);
    //sequences = merge_first_sub_sequences(sequences, initp);

    // Merge end two sub_sequences
    //sequences = merge_end_sub_sequences(sequences, initp);

    tcout<<endl<<"< < < Tree::sequences generation()";
    return sequences;
}

vector<vector<vector<int>>> Tree::divide_by_target_relation_based_on_StInG(C_Polyhedron & initp){
    tcout<<endl<<"> > > Tree::divide_by_target_relation_based_on_StInG()";
    vector<vector<vector<int>>> sequences;
    
    int ncl = vcl.size();
    vector<pair<int,int>> length_bound;
    vector<pair<int,int>>::iterator it;
    length_bound.push_back(make_pair(ncl-1,ncl-ra-er+0));
    length_bound.push_back(make_pair(ncl-ra-er-1+0,0));
    for (it=length_bound.begin();it<length_bound.end();it++){
        //tcout<<endl<<"1.";
        //Print_Location();
        Clear_Location_Invariant();
        //tcout<<endl<<"2.";
        //Print_Location();
        int length_hb = (*it).first;
        int length_lb = (*it).second;
        vector<vector<int>> sub_sequences;
        tcout<<endl;
        tcout<<endl<<"From hb:"<<length_hb<<" To lb:"<<length_lb;

        sub_sequences = dfs_sub_sequences_traverse_based_on_StInG(length_hb,length_lb,initp);

        tcout<<endl<<"sub_sequences.size()/capacity():"<<sub_sequences.size()<<"/"<<sub_sequences.capacity();
        tcout<<endl<<"This PRE_LOC has banged:"<<single_pre_prune_bang_count;
        sequences.push_back(sub_sequences);
        //tcout<<endl<<"3.";
        //Print_Location();
    }

    tcout<<endl<<"< < < Tree::divide_by_target_relation_based_on_StInG()";
    return sequences;
}

vector<vector<vector<int>>> Tree::no_divide_for_test(C_Polyhedron & initp){
    tcout<<endl<<"> > > Tree::no_divide_for_test()";
    vector<vector<vector<int>>> sequences;

    int ncl = vcl.size();
    vector<pair<int,int>> length_bound;
    vector<pair<int,int>>::iterator it;
    length_bound.push_back(make_pair(ncl-1,0));
    for (it=length_bound.begin();it<length_bound.end();it++){
        //tcout<<endl<<"1.";
        //Print_Location();
        Clear_Location_Invariant();
        //tcout<<endl<<"2.";
        //Print_Location();
        int length_hb = (*it).first;
        int length_lb = (*it).second;
        vector<vector<int>> sub_sequences;
        tcout<<endl;
        tcout<<endl<<"From hb:"<<length_hb<<" To lb:"<<length_lb;

        sub_sequences = dfs_sub_sequences_traverse_based_on_StInG(length_hb,length_lb,initp);

        tcout<<endl<<"sub_sequences.size()/capacity():"<<sub_sequences.size()<<"/"<<sub_sequences.capacity();
        tcout<<endl<<"This PRE_LOC has banged:"<<single_pre_prune_bang_count;
        sequences.push_back(sub_sequences);
        //tcout<<endl<<"3.";
        //Print_Location();
    }

    tcout<<endl<<"< < < Tree::no_divide_for_test()";
    return sequences;
}

vector<vector<vector<int>>> Tree::divide_by_target_relation(C_Polyhedron & initp){
    tcout<<endl<<"> > > Tree::divide_by_target_relation()";
    vector<vector<vector<int>>> sequences;
    
    int ncl = vcl.size();
    vector<pair<int,int>> length_bound;
    vector<pair<int,int>>::iterator it;
    length_bound.push_back(make_pair(ncl-1,ncl-ra-er+0));
    length_bound.push_back(make_pair(ncl-ra-er-1+0,0));
    for (it=length_bound.begin();it<length_bound.end();it++){
        int length_hb = (*it).first;
        int length_lb = (*it).second;
        vector<vector<int>> sub_sequences;
        tcout<<endl;
        tcout<<endl<<"From hb:"<<length_hb<<" To lb:"<<length_lb;

        sub_sequences = dfs_sub_sequences_traverse(length_hb,length_lb,initp);

        tcout<<endl<<"sub_sequences.size()/capacity():"<<sub_sequences.size()<<"/"<<sub_sequences.capacity();
        tcout<<endl<<"This PRE_LOC has banged:"<<single_pre_prune_bang_count;
        sequences.push_back(sub_sequences);
    }

    tcout<<endl<<"< < < Tree::divide_by_target_relation()";
    return sequences;
}

vector<vector<vector<int>>> Tree::one_per_group(C_Polyhedron & initp){
    tcout<<endl<<"> > > Tree::one_per_group()";
    vector<vector<vector<int>>> sequences;

    int ncl = vcl.size();
    vector<pair<int,int>> length_bound;
    vector<pair<int,int>>::iterator it;

    for (int i=ncl-1; i>=0; i=i-1){
        length_bound.push_back(make_pair(i,i));
    }

    for (it=length_bound.begin();it<length_bound.end();it++){
        int length_hb = (*it).first;
        int length_lb = (*it).second;
        vector<vector<int>> sub_sequences;
        tcout<<endl;
        tcout<<endl<<"From hb:"<<length_hb<<" To lb:"<<length_lb;

        sub_sequences = dfs_sub_sequences_traverse(length_hb,length_lb,initp);

        tcout<<endl<<"sub_sequences.size()/capacity():"<<sub_sequences.size()<<"/"<<sub_sequences.capacity();
        tcout<<endl<<"This PRE_LOC has banged:"<<single_pre_prune_bang_count;
        sequences.push_back(sub_sequences);
    }

    tcout<<endl;
    tcout<<endl<<"< < < Tree::one_per_group()";
    return sequences;
}

vector<vector<vector<int>>> Tree::two_per_group(C_Polyhedron & initp){
    tcout<<endl<<"> > > Tree::two_per_group()";
    vector<vector<vector<int>>> sequences;

    int ncl = vcl.size();
    vector<pair<int,int>> length_bound;
    vector<pair<int,int>>::iterator it;
    if (ncl % 2 == 0){
        for (int i=ncl-1; i>0; i=i-2){
            length_bound.push_back(make_pair(i,i-1));
        }
    }
    else {
        int i;
        length_bound.push_back(make_pair(ncl-1,ncl-1));
        for (i=ncl-1-1; i>0; i=i-2){
            length_bound.push_back(make_pair(i,i-1));
        }
        if (i==0){
            length_bound.push_back(make_pair(0,0));
        }
    }
    for (it=length_bound.begin();it<length_bound.end();it++){
        int length_hb = (*it).first;
        int length_lb = (*it).second;
        vector<vector<int>> sub_sequences;
        tcout<<endl;
        tcout<<endl<<"From hb:"<<length_hb<<" To lb:"<<length_lb;

        sub_sequences = dfs_sub_sequences_traverse(length_hb,length_lb,initp);

        tcout<<endl<<"sub_sequences.size()/capacity():"<<sub_sequences.size()<<"/"<<sub_sequences.capacity();
        tcout<<endl<<"This PRE_LOC has banged:"<<single_pre_prune_bang_count;
        sequences.push_back(sub_sequences);
    }

    tcout<<endl<<"< < < Tree::two_per_group()";
    return sequences;
}

vector<vector<vector<int>>> Tree::three_per_group(C_Polyhedron & initp){
    tcout<<endl<<"> > > Tree::three_per_group()";
    vector<vector<vector<int>>> sequences;

    int ncl = vcl.size();
    vector<pair<int,int>> length_bound;
    vector<pair<int,int>>::iterator it;

    int i = ncl;
    while (i - 3 >= 0){
        length_bound.push_back(make_pair(i-1,i-3));
        i = i - 3;
    }
    if (i > 0){
        length_bound.push_back(make_pair(i-1,0));
    }

    for (it=length_bound.begin();it<length_bound.end();it++){
        int length_hb = (*it).first;
        int length_lb = (*it).second;
        vector<vector<int>> sub_sequences;
        tcout<<endl;
        tcout<<endl<<"From hb:"<<length_hb<<" To lb:"<<length_lb;

        sub_sequences = dfs_sub_sequences_traverse(length_hb,length_lb,initp);

        tcout<<endl<<"sub_sequences.size()/capacity():"<<sub_sequences.size()<<"/"<<sub_sequences.capacity();
        tcout<<endl<<"This PRE_LOC has banged:"<<single_pre_prune_bang_count;
        sequences.push_back(sub_sequences);
    }

    tcout<<endl<<"< < < Tree::three_per_group()";
    return sequences;
}

vector<vector<vector<int>>> Tree::four_per_group(C_Polyhedron & initp){
    tcout<<endl<<"> > > Tree::four_per_group()";
    vector<vector<vector<int>>> sequences;

    int ncl = vcl.size();
    vector<pair<int,int>> length_bound;
    vector<pair<int,int>>::iterator it;

    int i = ncl;
    while (i - 4 >= 0){
        length_bound.push_back(make_pair(i-1,i-4));
        i = i - 4;
    }
    if (i > 0){
        length_bound.push_back(make_pair(i-1,0));
    }

    for (it=length_bound.begin();it<length_bound.end();it++){
        int length_hb = (*it).first;
        int length_lb = (*it).second;
        vector<vector<int>> sub_sequences;
        tcout<<endl;
        tcout<<endl<<"From hb:"<<length_hb<<" To lb:"<<length_lb;

        sub_sequences = dfs_sub_sequences_traverse(length_hb,length_lb,initp);

        tcout<<endl<<"sub_sequences.size()/capacity():"<<sub_sequences.size()<<"/"<<sub_sequences.capacity();
        tcout<<endl<<"This PRE_LOC has banged:"<<single_pre_prune_bang_count;
        sequences.push_back(sub_sequences);
    }

    tcout<<endl<<"< < < Tree::four_per_group()";
    return sequences;
}

vector<vector<vector<int>>> Tree::divide_target_into_double(C_Polyhedron & initp){
    tcout<<endl<<"> > > Tree::divide_target_into_double()";
    vector<vector<vector<int>>> sequences;

    int ncl = vcl.size();
    vector<pair<int,int>> length_bound;
    vector<pair<int,int>>::iterator it;
    int i;

    // related intra
    i = ncl - 1;
    length_bound.push_back(make_pair(i,i));
    i--;
    // related inter
    for ( ; i > ncl - (ra+er) - 1; i = i - 2){
        length_bound.push_back(make_pair(i,i-1));
    }
    // unrelated inter and intra
    for ( ; i >= 0; i = i - 1){
        length_bound.push_back(make_pair(i,i));
    }
    
    for (it=length_bound.begin();it<length_bound.end();it++){
        int length_hb = (*it).first;
        int length_lb = (*it).second;
        vector<vector<int>> sub_sequences;
        tcout<<endl;
        tcout<<endl<<"From hb:"<<length_hb<<" To lb:"<<length_lb;

        sub_sequences = dfs_sub_sequences_traverse(length_hb,length_lb,initp);

        tcout<<endl<<"sub_sequences.size()/capacity():"<<sub_sequences.size()<<"/"<<sub_sequences.capacity();
        tcout<<endl<<"This PRE_LOC has banged:"<<single_pre_prune_bang_count;
        sequences.push_back(sub_sequences);
    }

    tcout<<endl<<"< < < Tree::divide_target_into_double()";
    return sequences;
}

vector<vector<vector<int>>> Tree::divide_by_inter_transition(C_Polyhedron & initp){
    tcout<<endl<<"> > > Tree::divide_by_inter_transition()";
    vector<vector<vector<int>>> sequences;

    int ncl = vcl.size();
    vector<pair<int,int>> length_bound;
    vector<pair<int,int>>::iterator it;
    int i;

    // related intra
    i = ncl - ra;
    length_bound.push_back(make_pair(i,i));
    i--;
    // related and unrelated inter
    length_bound.push_back(make_pair(i,i-(er+uner)+1));
    i = i-(er+uner)+1 -1;
    // unrelated intra
    length_bound.push_back(make_pair(i,0));
    
    for (it=length_bound.begin();it<length_bound.end();it++){
        int length_hb = (*it).first;
        int length_lb = (*it).second;
        vector<vector<int>> sub_sequences;
        tcout<<endl;
        tcout<<endl<<"From hb:"<<length_hb<<" To lb:"<<length_lb;

        sub_sequences = dfs_sub_sequences_traverse(length_hb,length_lb,initp);

        tcout<<endl<<"sub_sequences.size()/capacity():"<<sub_sequences.size()<<"/"<<sub_sequences.capacity();
        tcout<<endl<<"This PRE_LOC has banged:"<<single_pre_prune_bang_count;
        sequences.push_back(sub_sequences);
    }

    tcout<<endl<<"< < < Tree::divide_by_inter_transition()";
    return sequences;
}

vector<vector<vector<int>>> Tree::divide_prior2_into_four(C_Polyhedron & initp){
    tcout<<endl<<"> > > Tree::divide_prior2_into_four()";
    vector<vector<vector<int>>> sequences;

    int ncl = vcl.size();
    vector<pair<int,int>> length_bound;
    vector<pair<int,int>>::iterator it;
    int i;

    // related intra
    i = ncl - ra;
    length_bound.push_back(make_pair(i,i));
    i--;
    // related inter
    if (er != 0){
        length_bound.push_back(make_pair(i,i-(er)+1));
        i = i-(er)+1 -1;
    }
    // unrelated inter
    if (uner != 0){
        length_bound.push_back(make_pair(i,i-(uner)+1));
        i = i-(uner)+1 -1;
    }
    // unrelated intra
    length_bound.push_back(make_pair(i,0));
    
    for (it=length_bound.begin();it<length_bound.end();it++){
        int length_hb = (*it).first;
        int length_lb = (*it).second;
        vector<vector<int>> sub_sequences;
        tcout<<endl;
        tcout<<endl<<"From hb:"<<length_hb<<" To lb:"<<length_lb;

        sub_sequences = dfs_sub_sequences_traverse(length_hb,length_lb,initp);

        tcout<<endl<<"sub_sequences.size()/capacity():"<<sub_sequences.size()<<"/"<<sub_sequences.capacity();
        tcout<<endl<<"This PRE_LOC has banged:"<<single_pre_prune_bang_count;
        sequences.push_back(sub_sequences);
    }

    tcout<<endl<<"< < < Tree::divide_prior2_into_four()";
    return sequences;
}

vector<vector<vector<int>>> Tree::merge_sub_sequences(vector<vector<vector<int>>> sequences, C_Polyhedron initp){
    tcout<<endl<<"> > > Tree::merge_sub_sequences()";
    tcout<<endl<<"| sequences.size(): "<<sequences.size();

    vector<vector<vector<int>>> merged_sequences;

    if (sequences.size() > 2){
        vector<vector<vector<int>>>::iterator it;
        int hb = vcl.size() - 1;
        int lb = vcl.size();
        if (sequences.size() % 2 == 0){
            for (it = sequences.begin(); it < sequences.end(); it = it + 2){
                hb = hb;
                lb = lb - (*(*it).begin()).size() - (*(*(it+1)).begin()).size();
                vector<vector<int>> merged_sub_sequences;
                merged_sub_sequences = Merge(*it, *(it+1), hb, lb, initp);
                merged_sequences.push_back(merged_sub_sequences);
                hb = hb - (*(*it).begin()).size() - (*(*(it+1)).begin()).size();
                lb = lb;
            }
        }
        else {
            for (it = sequences.begin(); it < sequences.end() - 1; it = it + 2){
                hb = hb;
                lb = lb - (*(*it).begin()).size() - (*(*(it+1)).begin()).size();
                vector<vector<int>> merged_sub_sequences;
                merged_sub_sequences = Merge(*it, *(it+1), hb, lb, initp);
                merged_sequences.push_back(merged_sub_sequences);
                hb = hb - (*(*it).begin()).size() - (*(*(it+1)).begin()).size();
                lb = lb;
            }
            if (it == sequences.end() - 1){
                merged_sequences.push_back(*it);
            }
        }
        merge_count++;
    }
    else {
        merged_sequences = sequences;
    }

    tcout<<endl<<"| merged_sequences.size(): "<<merged_sequences.size();
    tcout<<endl<<"< < < Tree::merge_sub_sequences()";
    return merged_sequences;
}

vector<vector<vector<int>>> Tree::merge_target_sub_sequences(vector<vector<vector<int>>> sequences, C_Polyhedron initp){
    tcout<<endl<<"> > > Tree::merge_target_sub_sequences()";
    tcout<<endl<<"| sequences.size(): "<<sequences.size();

    vector<vector<vector<int>>> merged_sequences;
    int ncl = vcl.size();
    int target_index = ncl-(ra+er)-1;

    if (sequences.size() > 2){
        vector<vector<vector<int>>>::iterator it;
        int hb = vcl.size() - 1;
        int lb = vcl.size();
        for (it=sequences.begin(); hb>target_index && it<sequences.end()-1; it=it+2){
            hb = hb;
            lb = lb - (*(*it).begin()).size() - (*(*(it+1)).begin()).size();
            vector<vector<int>> merged_sub_sequences;
            merged_sub_sequences = Merge(*it, *(it+1), hb, lb, initp);
            merged_sequences.push_back(merged_sub_sequences);
            hb = hb - (*(*it).begin()).size() - (*(*(it+1)).begin()).size();
            lb = lb;
        }
        for ( ; it<sequences.end(); it=it+1){
            merged_sequences.push_back(*it);
        }
        merge_count++;
    }
    else {
        merged_sequences = sequences;
    }

    tcout<<endl<<"| merged_sequences.size(): "<<merged_sequences.size();
    tcout<<endl<<"< < < Tree::merge_target_sub_sequences()";
    return merged_sequences;
}

vector<vector<vector<int>>> Tree::merge_first_sub_sequences(vector<vector<vector<int>>> sequences, C_Polyhedron initp){
    tcout<<endl<<"> > > Tree::merge_first_sub_sequences()";
    tcout<<endl<<"| sequences.size(): "<<sequences.size();

    vector<vector<vector<int>>> merged_sequences;
    int ncl = vcl.size();
    //int target_index = ncl-(ra+er)-1;

    if (sequences.size() > 2){
        vector<vector<vector<int>>>::iterator it;
        int hb = vcl.size() - 1;
        int lb = vcl.size();
        it=sequences.begin();
        //for (it=sequences.begin(); hb>target_index && it<sequences.end()-1; it=it+2){
            hb = hb;
            lb = lb - (*(*it).begin()).size() - (*(*(it+1)).begin()).size();
            vector<vector<int>> merged_sub_sequences;
            merged_sub_sequences = Merge(*it, *(it+1), hb, lb, initp);
            merged_sequences.push_back(merged_sub_sequences);
            //hb = hb - (*(*it).begin()).size() - (*(*(it+1)).begin()).size();
            //lb = lb;
        //}
        it = it + 2;
        for ( ; it<sequences.end(); it=it+1){
            merged_sequences.push_back(*it);
        }
        merge_count++;
    }
    else {
        merged_sequences = sequences;
    }

    tcout<<endl<<"| merged_sequences.size(): "<<merged_sequences.size();
    tcout<<endl<<"< < < Tree::merge_first_sub_sequences()";
    return merged_sequences;
}

vector<vector<vector<int>>> Tree::merge_end_sub_sequences(vector<vector<vector<int>>> sequences, C_Polyhedron initp){
    tcout<<endl<<"> > > Tree::merge_end_sub_sequences()";
    tcout<<endl<<"| sequences.size(): "<<sequences.size();

    vector<vector<vector<int>>> merged_sequences;
    int ncl = vcl.size();
    //int target_index = ncl-(ra+er)-1;

    if (sequences.size() > 2){
        vector<vector<vector<int>>>::iterator it;
        
        for (it=sequences.begin(); it<sequences.end()-2; it=it+1){
            merged_sequences.push_back(*it);
        }

        int hb = 0 - 1;
        int lb = 0;
        //for (it=sequences.begin(); hb>target_index && it<sequences.end()-1; it=it+2){
            hb = hb + (*(*it).begin()).size() + (*(*(it+1)).begin()).size();
            lb = lb;
            vector<vector<int>> merged_sub_sequences;
            merged_sub_sequences = Merge(*it, *(it+1), hb, lb, initp);
            merged_sequences.push_back(merged_sub_sequences);
            //hb = hb - (*(*it).begin()).size() - (*(*(it+1)).begin()).size();
            //lb = lb;
        //}

        merge_count++;
    }
    else {
        merged_sequences = sequences;
    }

    tcout<<endl<<"| merged_sequences.size(): "<<merged_sequences.size();
    tcout<<endl<<"< < < Tree::merge_end_sub_sequences()";
    return merged_sequences;
}

vector<vector<int>> Tree::Merge(vector<vector<int>> sub_sequences1, vector<vector<int>> sub_sequences2, int hb, int lb, C_Polyhedron initp){
    vector<vector<int>> merged_sub_sequences;
    bang_count_in_merge = 0;

    vector<vector<vector<int>>> two_sub_sequences;
    two_sub_sequences.push_back(sub_sequences1);
    two_sub_sequences.push_back(sub_sequences2);
    int start = -1;
    int depth = hb;
    vector<int> sequence;
    Clump invd_vp(fd);
    single_merge_sub_sequences_timer.restart();
    //Merge_recursive(two_sub_sequences, merged_sub_sequences, start, sequence, initp, invd_vp, hb, lb);
    Merge_recursive2(two_sub_sequences, merged_sub_sequences, sequence, start, depth, initp, invd_vp, hb, lb);
    single_merge_sub_sequences_timer.stop();
    int single_merge_sub_sequences_time = single_merge_sub_sequences_timer.compute_time_elapsed();

    tcout<<endl<<"| hb:"<<hb<<", lb:"<<lb<<", weave_in_merge:"<<invd_vp.get_count()<<", bang_in_merge:"<<bang_count_in_merge<<", time:"<<single_merge_sub_sequences_time;
    tcout<<endl<<"merged_sub_sequences.capacity():"<<merged_sub_sequences.capacity();
    tcout<<endl<<"merged_sub_sequences.size():"<<merged_sub_sequences.size();
    return merged_sub_sequences;
}

void Tree::Merge_recursive2(vector<vector<vector<int>>> two_sub_sequences, vector<vector<int>> & merged_sub_sequences, vector<int> & sequence, int i, int depth,C_Polyhedron & cpoly, Clump & invd_vp, int hb, int lb){

    if ( i == two_sub_sequences.size() - 1 ){
        //tcout<<endl;
        //tcout<<endl<<"/-----------------------------";
        //Print_Prune_Sequence_Tree(sequence, lb, hb, lb,"Weaved");
        collect_timer.restart();
        //collect_invariant_polys(cpoly, invd_vp);
        //merged_sub_sequences.push_back(sequence);
        collect_invariant_polys_and_sub_sequences(invd_vp,merged_sub_sequences,cpoly,sequence);
        collect_timer.stop();
        tcout<<endl<<"- The collect_invariant_polys_and_sub_sequences Time Taken (0.01s) = "<<collect_timer.compute_time_elapsed();
        //tcout<<endl<<"\\-----------------------------"<<endl;
        return;
    }

    int j = 0;
    vector<int> banged_s;
    bool s_banged_flag = false;
    while ( j < two_sub_sequences[i+1].size() ){
        vector<int> s;
        s.insert(s.end(), two_sub_sequences[i+1][j].begin(), two_sub_sequences[i+1][j].end());

        if (banged_s.size() > 0 && has_the_same_sequences_from_the_left(banged_s, s)){
            j++;
            continue;
        }
        else {
            banged_s.clear();
            s_banged_flag = false;
        }

        C_Polyhedron p(cpoly);
        int index = 0;
        vector<int> temp_s;
        vector<int> read_s = sequence;

        for (vector<int>::iterator it = s.begin(); it < s.end(); it++){
            temp_s.push_back(*it);
            read_s.push_back(*it);
            p.intersection_assign(get_clump(depth-index).get_reference(*it));
            if (invd_vp.contains(p)){
                //Print_Prune_Sequence_Tree(read_s, depth-index, hb, lb, "Banged");
                bang_count++;
                single_pre_prune_bang_count++;
                bang_count_in_merge++;

                banged_s = temp_s;
                s_banged_flag = true;
                break;
            }
            index++;
        }

        if (s_banged_flag != true){
            Merge_recursive2(two_sub_sequences, merged_sub_sequences, read_s, i+1, depth-index, p, invd_vp, hb, lb);
        }
        else {
            ;
        }
        j++;
    }
    return;
}
/*
void Tree::Merge_recursive(vector<vector<vector<int>>> two_sub_sequences, vector<vector<int>> & merged_sub_sequences, int i, vector<int> sequence, C_Polyhedron initp, Clump & invd_vp, int hb, int lb){
    if (i == two_sub_sequences.size() - 1){
        read_and_collect_a_sequence(merged_sub_sequences, sequence, initp, invd_vp, hb, lb);
        return;
    }
    int j=0;
    while (j < two_sub_sequences[i+1].size()){
        vector<int> s = sequence;
        s.insert(s.end(), two_sub_sequences[i+1][j].begin(), two_sub_sequences[i+1][j].end());
        Merge_recursive(two_sub_sequences, merged_sub_sequences, i+1, s, initp, invd_vp, hb, lb);
        j++;
    }
    return;
}
*/
/*
void Tree::read_and_collect_a_sequence(vector<vector<int>> & merged_sub_sequences, vector<int> sequence, C_Polyhedron cpoly, Clump & invd_vp, int hb, int lb){
    //tcout<<endl<<"> > > Tree::read_and_collect_a_sequence()";
    //tcout<<endl<<"sequence.size(): "<<sequence.size();
    //tcout<<endl<<"hb - lb + 1: "<<hb - lb + 1;
    if (sequence.size() == hb - lb + 1){
        C_Polyhedron p(cpoly);
        int dth, i=0, j;
        for (dth = hb; dth >= lb; dth--){
            j = sequence[i];
            p.intersection_assign(get_clump(dth).get_reference(j));
            if (invd_vp.contains(p)){
                Print_Prune_Sequence_Tree(sequence, dth, hb, lb, "Banged");
                bang_count++;
                single_pre_prune_bang_count++;
                return;
            }
            i++;
            if (dth == lb){
                tcout<<endl;
                tcout<<endl<<"/-----------------------------";
                Print_Prune_Sequence_Tree(sequence, dth, hb, lb,"Weaved");
                collect_invariant_polys(p, invd_vp);
                merged_sub_sequences.push_back(sequence);
                tcout<<endl<<"\\-----------------------------";
                tcout<<endl;
                return;
            }
        }
    }
    else {
        tcout<<endl<<"Sequence Length Error";
    }
    //tcout<<endl<<"< < < Tree::read_and_collect_a_sequence()";
}
*/
vector<vector<int>> Tree::dfs_sub_sequences_traverse_based_on_StInG(int hb,int lb, C_Polyhedron & initp){
    tcout<<endl<<"> > > Tree::dfs_sub_sequences_traverse_based_on_StInG()";
    vector<vector<int>> sub_sequences;

    // Test for writing sequences
    /*
    tcout<<endl<<"hb:"<<hb<<",lb:"<<lb;
    vector<int> s;
    int i=0,dth;
    for (dth=hb; dth>=lb; dth--){
        s.push_back(7);
        tcout<<endl<<"s["<<i<<"]:"<<s[i];
        i++;
    }
    tcout<<endl<<"size of s:"<<s.size();
    sub_sequences.push_back(s);
    */

    C_Polyhedron invd(*trivial);
    int depth = hb+1;
    dfs_sub_sequences_traverse_recursive_based_on_StInG(sub_sequences,hb,lb,depth,initp,invd);

    tcout<<endl<<"< < < Tree::dfs_sub_sequences_traverse_based_on_StInG()";
    return sub_sequences;
}

vector<vector<int>> Tree::dfs_sub_sequences_traverse(int hb,int lb, C_Polyhedron & initp){
    tcout<<endl<<"> > > Tree::dfs_sub_sequences_traverse()";
    vector<vector<int>> sub_sequences;

    // Test for writing sequences
    /*
    tcout<<endl<<"hb:"<<hb<<",lb:"<<lb;
    vector<int> s;
    int i=0,dth;
    for (dth=hb; dth>=lb; dth--){
        s.push_back(7);
        tcout<<endl<<"s["<<i<<"]:"<<s[i];
        i++;
    }
    tcout<<endl<<"size of s:"<<s.size();
    sub_sequences.push_back(s);
    */

    //C_Polyhedron invd(*trivial);
    Clump invd_vp(fd);
    int depth = hb+1;
    dfs_sub_sequences_traverse_recursive(sub_sequences,hb,lb,depth,initp,invd_vp);

    tcout<<endl<<"This sub_sequences invd_vp has weaved:"<<invd_vp.get_count();
    tcout<<endl<<"< < < Tree::dfs_sub_sequences_traverse()";
    return sub_sequences;
}

void Tree::dfs_sub_sequences_traverse_recursive_based_on_StInG(vector<vector<int>> & sub_sequences,int hb,int lb,int depth,C_Polyhedron & cpoly,C_Polyhedron & invd){
    //tcout<<endl<<"> > > Tree::dfs_sub_sequences_traverse_recursive_based_on_StInG()";
    
    //tcout<<endl<<"depth:"<<depth<<", cpoly:";
    //tcout<<endl<<cpoly;

    if (invd.contains(cpoly)){
        //tcout<<endl<<"invd:"<<endl<<invd;
        //tcout<<endl<<"cpoly:"<<endl<<cpoly;
        Print_Prune_Tree(depth,hb,lb,"Banged"); // print for debug and improve algorithm
        bang_count++;
        return;
    }

    if (depth==lb){
        //backtrack_flag = true;
        tcout<<endl;
        tcout<<endl<<"/-----------------------------";
        Print_Prune_Tree(depth,hb,lb,"Weaved");
        collect_invariants(cpoly,invd);
        collect_sub_sequences(sub_sequences,hb,lb);
        //tcout<<endl<<"4.";
        //Print_Location();
        tcout<<endl<<"\\-----------------------------";
        tcout<<endl;
        return;
    }

    get_clump(depth-1).clear();
    while(get_clump(depth-1).has_next()){
        //tcout<<endl<<"in while...next()";
        //tcout<<endl<<"depth:"<<depth<<", cpoly:";
        //tcout<<endl<<cpoly;
        C_Polyhedron p(cpoly);
        p.intersection_assign(get_clump(depth-1).get_reference());
        dfs_sub_sequences_traverse_recursive_based_on_StInG(sub_sequences,hb,lb,depth-1,p,invd);
        if (backtrack_flag == true){
            if (invd.contains(cpoly)){
                backtrack_success++;
                tcout<<endl<<"Pruned by backtracking in depth "<<depth;
                get_clump(depth-1).clear();
                return;
            }
            else {
                if (backtrack_success >= 1){
                    backtrack_count++;
                    backtrack_success = 0;
                }
                backtrack_flag = false;
            }
        }
        get_clump(depth-1).next();
    }

    //tcout<<endl<<"< < < Tree::dfs_sub_sequences_traverse_recursive_based_on_StInG()";
    return;
}

void Tree::dfs_sub_sequences_traverse_recursive(vector<vector<int>> & sub_sequences,int hb,int lb,int depth,C_Polyhedron & cpoly,Clump & invd_vp){
    //tcout<<endl<<"> > > Tree::dfs_sub_sequences_traverse_recursive()";
    
    //tcout<<endl<<"depth:"<<depth<<", cpoly:";
    //tcout<<endl<<cpoly;
    if (total_timer.compute_time_elapsed() >= total_time){
        tcout<<endl<<"Time is up!";
        return;
    }

    if (invd_vp.contains(cpoly)){
        bang_count++;
        single_pre_prune_bang_count++;
        counter.set_pre_pbc_at_location_and_depth(get_target_index(), depth);

        //tcout<<endl<<"invd:"<<endl<<invd;
        //tcout<<endl<<"cpoly:"<<endl<<cpoly;
        if(print_tree){
            Print_Prune_Tree(depth,hb,lb,"Banged"); // print for debug and improve algorithm
        }
        return;
    }

    if (depth==lb){
        //backtrack_flag = true;
        //tcout<<endl;
        //tcout<<endl<<"/-----------------------------";
        if(print_tree){
            Print_Prune_Tree(depth,hb,lb,"Weaved");
        }
        collect_timer.restart();
        //collect_invariant_polys(cpoly,invd_vp);
        //collect_sub_sequences(sub_sequences,hb,lb);
        collect_invariant_polys_and_sub_sequences(invd_vp,sub_sequences,cpoly,hb,lb);
        collect_timer.stop();
        //tcout<<endl<<"- The collect_invariant_polys_and_sub_sequences Time Taken (0.01s) = "<<collect_timer.compute_time_elapsed();
        //tcout<<endl<<"4.";
        //Print_Location();
        //tcout<<endl<<"\\-----------------------------";
        //tcout<<endl;
        return;
    }

    get_clump(depth-1).clear();
    while(get_clump(depth-1).has_next()){
        //tcout<<endl<<"in while...next()";
        //tcout<<endl<<"depth:"<<depth<<", cpoly:";
        //tcout<<endl<<cpoly;
        C_Polyhedron p(cpoly);
        p.intersection_assign(get_clump(depth-1).get_reference());
        dfs_sub_sequences_traverse_recursive(sub_sequences,hb,lb,depth-1,p,invd_vp);
        if (backtrack_flag == true){
            if (invd_vp.contains(cpoly)){
                backtrack_success++;
                tcout<<endl<<"Pruned by backtracking in depth "<<depth;
                get_clump(depth-1).clear();
                return;
            }
            else {
                if (backtrack_success >= 1){
                    backtrack_count++;
                    backtrack_success = 0;
                }
                backtrack_flag = false;
            }
        }
        get_clump(depth-1).next();
    }

    //tcout<<endl<<"< < < Tree::dfs_sub_sequences_traverse_recursive()";
    return;
}

void Tree::collect_invariant_polys(C_Polyhedron & cpoly,Clump & invd_vp){
    invd_vp.insert(cpoly);
    tcout<<endl<<"  invd_vp.size():"<<invd_vp.get_count();
}

void Tree::collect_sub_sequences(vector<vector<int>> & sub_sequences, int hb, int lb){
    //tcout<<endl<<"> > > Tree::collect_sub_sequences()";

    vector<int> s;
    int dth;
    for (dth=hb; dth>=lb; dth--){
        s.push_back(get_clump(dth).get_gli());
    }
    tcout<<endl<<"- s.size():"<<s.size();
    tcout<<endl<<"  s:";
    for (int i=0; i<s.size(); i++){
        tcout<<s[i];
    }
    sub_sequences.push_back(s);
    //tcout<<endl<<"< < < Tree::collect_sub_sequences()";
}

void Tree::collect_invariant_polys_and_sub_sequences(Clump & invd_vp,vector<vector<int>> & sub_sequences,C_Polyhedron & cpoly,int hb,int lb){
    //tcout<<endl<<"> > > Tree::collect_invariant_polys_and_sub_sequences()";

    //  collect sub_sequences
    vector<int> s;
    int dth;
    for (dth=hb; dth>=lb; dth--){
        s.push_back(get_clump(dth).get_gli());
    }
    //tcout<<endl<<"- s.size():"<<s.size();
    //tcout<<endl<<"  s:";
    //for (int i=0; i<s.size(); i++){
    //    tcout<<s[i];
    //}

    //  collect invd_vp
    vector<int> erase_index;
    erase_index = invd_vp.insert_with_erase_index(cpoly);
    //tcout<<endl<<"  invd_vp.size():"<<invd_vp.get_count();

    //  add above collectors
    vector<int>::reverse_iterator vi;
    for (vi = erase_index.rbegin(); vi < erase_index.rend(); vi++){
        sub_sequences.erase(sub_sequences.begin()+(*vi));
    }
    sub_sequences.push_back(s);

    //tcout<<endl<<"< < < Tree::collect_invariant_polys_and_sub_sequences()";
    return;
}

void Tree::collect_invariant_polys_and_sub_sequences(Clump & invd_vp,vector<vector<int>> & sub_sequences,C_Polyhedron & cpoly,vector<int> & sequence){
    //tcout<<endl<<"> > > Tree::collect_invariant_polys_and_sub_sequences()";

    //  collect sub_sequences
    tcout<<endl<<"- sequence.size():"<<sequence.size();
    tcout<<endl<<"  sequence:";
    for (int i=0; i<sequence.size(); i++){
        tcout<<sequence[i];
    }

    //  collect invd_vp
    vector<int> erase_index;
    erase_index = invd_vp.insert_with_erase_index(cpoly);
    tcout<<endl<<"  invd_vp.size():"<<invd_vp.get_count();

    //  add above collectors
    vector<int>::reverse_iterator vi;
    for (vi = erase_index.rbegin(); vi < erase_index.rend(); vi++){
        sub_sequences.erase(sub_sequences.begin()+(*vi));
    }
    sub_sequences.push_back(sequence);

    //tcout<<endl<<"< < < Tree::collect_invariant_polys_and_sub_sequences()";
    return;
}

/*
void Tree::collect_invariant_polys_and_sub_sequences(Clump & invd_vp,vector<vector<int>> & sub_sequences,C_Polyhedron & cpoly,int hb,int lb){
    //tcout<<endl<<"> > > Tree::collect_invariant_polys_and_sub_sequences()";

    vector<int> s;
    int dth;
    for (dth=hb; dth>=lb; dth--){
        s.push_back(get_clump(dth).get_gli());
    }
    tcout<<endl<<"- s.size():"<<s.size();
    tcout<<endl<<"  s:";
    for (int i=0; i<s.size(); i++){
        tcout<<s[i];
    }

    vector<C_Polyhedron> vp;
    vector<C_Polyhedron>::iterator vi;
    vector<vector<int>>::iterator vj;
    vp = invd_vp.get_vp();

    for (vi=vp.begin(),vj=sub_sequences.begin();vi<vp.end();++vi,++vj){
        if ((*vi).contains(cpoly)){
            tcout<<endl<<"Wrong Type: (*vi).contains(cpoly)";
            return;
        }
        else if (cpoly.contains(*vi)){
            //tcout<<endl<<"cpoly.contains(*vi)";
            vi=vp.erase(vi);
            vi--;
            vj=sub_sequences.erase(vj);
            vj--;
        }
    }

    vp.push_back(cpoly);
    invd_vp.replace_vp(vp);
    sub_sequences.push_back(s);
    tcout<<endl<<"  invd_vp.size():"<<invd_vp.get_count();

    //tcout<<endl<<"< < < Tree::collect_invariant_polys_and_sub_sequences()";
    return;
}

void Tree::collect_invariant_polys_and_sub_sequences(Clump & invd_vp,vector<vector<int>> & sub_sequences,C_Polyhedron & cpoly,vector<int> & sequence){
    //tcout<<endl<<"> > > Tree::collect_invariant_polys_and_sub_sequences()";

    tcout<<endl<<"- sequence.size():"<<sequence.size();
    tcout<<endl<<"  sequence:";
    for (int i=0; i<sequence.size(); i++){
        tcout<<sequence[i];
    }

    vector<C_Polyhedron> vp;
    vector<C_Polyhedron>::iterator vi;
    vector<vector<int>>::iterator vj;
    vp = invd_vp.get_vp();

    for (vi=vp.begin(),vj=sub_sequences.begin();vi<vp.end();++vi,++vj){
        if ((*vi).contains(cpoly)){
            tcout<<endl<<"Wrong Type: (*vi).contains(cpoly)";
            return;
        }
        else if (cpoly.contains(*vi)){
            //tcout<<endl<<"cpoly.contains(*vi)";
            vi=vp.erase(vi);
            vi--;
            vj=sub_sequences.erase(vj);
            vj--;
        }
    }

    vp.push_back(cpoly);
    invd_vp.replace_vp(vp);
    sub_sequences.push_back(sequence);
    tcout<<endl<<"  invd_vp.size():"<<invd_vp.get_count();

    //tcout<<endl<<"< < < Tree::collect_invariant_polys_and_sub_sequences()";
    return;
}
*/
void Tree::dfs_sequences_traverse(vector<vector<vector<int>>> sequences, C_Polyhedron & initp, C_Polyhedron & invd){
    tcout<<endl<<"> > > Tree::dfs_sequences_traverse()";

    // Test for reading sequences
    /*
    tcout<<endl<<"- sequences.size():"<<sequences.size();
    for (int i=0; i<sequences.size(); i++){
        tcout<<endl<<"- - sequence["<<i<<"].size():"<<sequences[i].size();

        for (int j=0; j<sequences[i].size(); j++){
            tcout<<endl<<"- - - sequences["<<i<<"]["<<j<<"].size():"<<sequences[i][j].size();

            for (int k=0; k<sequences[i][j].size(); k++){
                tcout<<endl<<"      sequences["<<i<<"]["<<j<<"]["<<k<<"]:"<<sequences[i][j][k];
            }
        }
    }
    */

    int start = -1;
    vector<int> sequence;
    int depth = vcl.size()-1;
    dfs_sequences_traverse_recursive2(sequence, sequences, start, depth, initp, invd);
    //  Old dfs_sequences_traverse_recursive
    //vector<int> sequence;
    //dfs_sequences_traverse_recursive(sequence, sequences, start, initp, invd);

    tcout<<endl<<"< < < Tree::dfs_sequences_traverse()";
}

void Tree::dfs_sequences_traverse_recursive2(vector<int> & sequence, vector<vector<vector<int>>> sequences, int i, int depth, C_Polyhedron & cpoly, C_Polyhedron & invd){

    if (total_timer.compute_time_elapsed() >= total_time){
        tcout<<endl<<"Time is up!";
        return;
    }

    if ( i == sequences.size() - 1 ){
        weave_count++;
        single_weave_count++;

        tcout<<endl;
        tcout<<endl<<"sequence:";
        for (int k=0; k<sequence.size(); k++){
            tcout<<sequence[k];
        }
        tcout<<endl<<"/-----------------------------";
        if(print_tree){
            Print_Prune_Sequence_Tree(sequence, 0, "Weaved");
        }
        collect_timer.restart();
        collect_invariants_for_one_location_by_eliminating(target_index, cpoly, invd);
        tcout<<endl;
        tcout<<endl<<"- Have Collected "<<weave_count<<" invariant(s)";
        collect_timer.stop();
        tcout<<endl<<"- The collect_invariants Time Taken (0.01s) = "<<collect_timer.compute_time_elapsed();
        collect_time = collect_time + collect_timer.compute_time_elapsed();
        single_collect_time = single_collect_time + collect_timer.compute_time_elapsed();
        if (debug == 1){
            tcout<<endl<<"------------------------------";
            tcout<<endl<<"- cpoly: "<<endl<<"  "<<cpoly;
            tcout<<endl<<"- invd: "<<endl<<"  "<<invd;
            tcout<<endl<<"- invariant: "<<endl<<"  "<<(*loclist)[target_index]->get_invariant();
        }
        tcout<<endl<<"\\-----------------------------";
        return;
    }

    int j = 0;
    vector<int> banged_s;
    bool s_banged_flag = false;
    while ( j < sequences[i+1].size() ){
        vector<int> s;
        s.insert(s.end(), sequences[i+1][j].begin(), sequences[i+1][j].end());

        if (banged_s.size() > 0 && has_the_same_sequences_from_the_left(banged_s, s)){
            j++;
            continue;
        }
        else {
            banged_s.clear();
            s_banged_flag = false;
        }

        C_Polyhedron p(cpoly);
        int index = 0;
        vector<int> temp_s;
        vector<int> read_s = sequence;

        for (vector<int>::iterator it = s.begin(); it < s.end(); it++){
            temp_s.push_back(*it);
            read_s.push_back(*it);
            p.intersection_assign(get_clump(depth-index).get_reference(*it));
            if (invd.contains(p)){
                bang_count++;
                single_post_prune_bang_count++;
                counter.set_pst_pbc_at_location_and_depth(get_target_index(), depth-index);

                //tcout<<endl;
                //tcout<<endl<<"sequence:";
                for (int k=0; k<read_s.size(); k++){
                    //tcout<<read_s[k];
                }
                if(print_tree){
                    Print_Prune_Sequence_Tree(read_s, depth-index, "Banged");
                }
                if (debug == 1){
                    tcout<<endl<<"------------------------------";
                    tcout<<endl<<"- cpoly: "<<endl<<"  "<<cpoly;
                    tcout<<endl<<"- invd: "<<endl<<"  "<<invd;
                    tcout<<endl<<"- invariant: "<<endl<<"  "<<(*loclist)[target_index]->get_invariant();
                    tcout<<endl<<"\\-----------------------------";
                }

                banged_s = temp_s;
                s_banged_flag = true;
                break;
            }
            index++;
        }

        if (s_banged_flag != true){
            dfs_sequences_traverse_recursive2(read_s, sequences, i+1, depth-index, p, invd);
        }
        else {
            ;
        }
        j++;
    }
    return;
}

bool Tree::has_the_same_sequences_from_the_left(vector<int> banged_s, vector<int> s){
    for (int i=0; i<banged_s.size(); i++){
        if (banged_s[i] != s[i]){
            return false;
        }
    }
    return true;
}
/*
void Tree::dfs_sequences_traverse_recursive(vector<int> & sequence, vector<vector<vector<int>>> sequences, int i, C_Polyhedron & initp, C_Polyhedron & invd){
    //tcout<<endl<<"> > > Tree::dfs_sequences_traverse_recursive()";

    if (i == sequences.size()-1){
        tcout<<endl;
        tcout<<endl<<"sequence:";
        for (int k=0; k<sequence.size(); k++){
            tcout<<sequence[k];
        }
        read_a_sequence(sequence, initp, invd);
        return;
    }
    int j=0;
    while (j<sequences[i+1].size()){
        vector<int> s = sequence;
        s.insert(s.end(), sequences[i+1][j].begin(), sequences[i+1][j].end());
        dfs_sequences_traverse_recursive(s, sequences, i+1, initp, invd);
        j++;
    }

    //tcout<<endl<<"< < < Tree::dfs_sequences_traverse_recursive()";
    return;
}
*/
/*
void Tree::read_a_sequence(vector<int> sequence, C_Polyhedron & cpoly, C_Polyhedron & invd){
    //tcout<<endl<<"> > > Tree::read_a_sequence()";

    //C_Polyhedron invd(*trivial);
    if (sequence.size() == size()){
        C_Polyhedron p(cpoly);
        int dth, i=0;
        for (dth=sequence.size()-1;dth>=0;dth--){
            int j=sequence[i];
            p.intersection_assign(get_clump(dth).get_reference(j));
            if (invd.contains(p)){
                Print_Prune_Sequence_Tree(sequence, dth,"Banged");
                bang_count++;
                single_post_prune_bang_count++;
                return;
            }
            i++;

            if (dth == 0){
                weave_count++;
                single_weave_count++;

                tcout<<endl<<"/-----------------------------";
                Print_Prune_Sequence_Tree(sequence, dth, "Weaved");
                collect_timer.restart();
                collect_invariants_for_one_location_by_eliminating(target_index, p, invd);
                tcout<<endl;
                tcout<<endl<<"- Have Collected "<<weave_count<<" invariant(s)";
                collect_timer.stop();
                tcout<<endl<<"- The collect_invariants Time Taken (0.01s) = "<<collect_timer.compute_time_elapsed();
                collect_time = collect_time + collect_timer.compute_time_elapsed();
                single_collect_time = single_collect_time + collect_timer.compute_time_elapsed();
                tcout<<endl<<"\\-----------------------------"<<endl;
                return;
            }
        }
    }
    else{
        tcout<<endl<<"Sequence Length Error!";
    }

    //tcout<<endl<<"< < < Tree::read_a_sequence()";
}
*/