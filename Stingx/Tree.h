
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
 * Filename: Tree.cc
 * Author: Hongming Liu<hm-liu@sjtu.edu.cn>
 * Comments: Some method about converting CNF to DNF.
 * Copyright: Please see README file.
 */


#ifndef __TREE__H_
#define __TREE__H_

#include <vector>
#include <iostream>
#include <algorithm>
#include "ppl.hh"
#include "Clump.h"
#include "Location.h"
#include "TransitionRelation.h"
#include "ToolUtils.h"

using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;

class Tree{
    
    private:
        vector<Clump> vcl;
        void initialize(vector<Clump> & outer_vcl);
        int ra;//related location(intra)
        int er;//related transition(inter)
        int unra;//un-related location(intra)
        int uner;//un-related transition(inter)
        int target_index=-1;
        int max_clump_count=-1;

        vector<pair<int,vector<int>> > pruned_node;
        vector<int> clumps_gli;
        vector<int> conflict_depth;
        int first_conflict = -1;

    public:
        Tree();
        Tree(vector<Clump> & outer_vcl);
        void set_tree(vector<Clump> & outer_vcl);
        vector<Clump> & get_tree();
        int size();
        void set_ra(int amount);
        void set_er(int amount);
        void set_unra(int amount);
        void set_uner(int amount);
        void set_target_index(int index);
        void set_max_clump_count();
        int get_ra();
        int get_er();
        int get_unra();
        int get_uner();
        int get_target_index();
        int get_max_clump_count();
        Clump & get_clump(int depth);
        void Original_Prior(vector<Clump> &outer_vcl);
        void Reorder_Target_Prior_1(vector<Clump> &outer_vcl);
        void Reorder_Target_Prior_2(vector<Clump> &outer_vcl);
        void Reorder_Target_Prior_3(vector<Clump> &outer_vcl);
        void extract_vcl_for_one_location_about_intra(vector<Clump> &outer_vcl);
        void Print_Prune_Tree(int depth, string weavedorbanged);
        void Print_Prune_Tree(int depth, int hb, int lb, string weavedorbanged);
        void Print_Prune_Sequence_Tree(vector<int> sequence, int depth, string weavedorbanged);
        void Print_Prune_Sequence_Tree(vector<int> sequence, int depth, int hb, int lb, string weavedorbanged);

        // prune method 1
        void prune_node_self_inspection(int target_index, C_Polyhedron & invd);
        void insert_pruned_node(int depth, vector<int> node_gli);
        void clear_pruned_node();
        void store_conflict_node();
        void store_clumps_gli();
        int get_first_conflict();
        void clear_first_conflict();

        // prune method 2
        void prune_clumps_by_hierarchy_inclusion();

        // dfs_sequences_traverse
        vector<vector<vector<int>>> sequences_generation(string divide_into_sections, C_Polyhedron & initp);
        vector<vector<vector<int>>> divide_by_target_relation_based_on_StInG(C_Polyhedron & initp);
        vector<vector<vector<int>>> no_divide_for_test(C_Polyhedron & initp);
        vector<vector<vector<int>>> divide_by_target_relation(C_Polyhedron & initp);
        vector<vector<vector<int>>> one_per_group(C_Polyhedron & initp);
        vector<vector<vector<int>>> two_per_group(C_Polyhedron & initp);
        vector<vector<vector<int>>> three_per_group(C_Polyhedron & initp);
        vector<vector<vector<int>>> four_per_group(C_Polyhedron & initp);
        vector<vector<vector<int>>> divide_target_into_double(C_Polyhedron & initp);
        vector<vector<vector<int>>> divide_by_inter_transition(C_Polyhedron & initp);
        vector<vector<vector<int>>> divide_prior2_into_four(C_Polyhedron & initp);
        vector<vector<vector<int>>> merge_sub_sequences(vector<vector<vector<int>>> sequences, C_Polyhedron initp);
        vector<vector<vector<int>>> merge_target_sub_sequences(vector<vector<vector<int>>> sequences, C_Polyhedron initp);
        vector<vector<vector<int>>> merge_first_sub_sequences(vector<vector<vector<int>>> sequences, C_Polyhedron initp);
        vector<vector<vector<int>>> merge_end_sub_sequences(vector<vector<vector<int>>> sequences, C_Polyhedron initp);
        vector<vector<int>> Merge(vector<vector<int>> sub_sequences1, vector<vector<int>> sub_sequences2, int hb, int lb, C_Polyhedron initp);
        void Merge_recursive2(vector<vector<vector<int>>> two_sub_sequences, vector<vector<int>> & merged_sub_sequences, vector<int> & sequence, int i, int depth,C_Polyhedron & cpoly, Clump & invd_vp, int hb, int lb);
        //void Merge_recursive(vector<vector<vector<int>>> two_sub_sequences, vector<vector<int>> & merged_sub_sequences, int i, vector<int> sequence, C_Polyhedron initp, Clump & invd_vp, int hb, int lb);
        //void read_and_collect_a_sequence(vector<vector<int>> & merged_sub_sequences, vector<int> sequence, C_Polyhedron cpoly, Clump & invd_vp, int hb, int lb);
        vector<vector<int>> dfs_sub_sequences_traverse_based_on_StInG(int hb,int lb, C_Polyhedron & initp);
        vector<vector<int>> dfs_sub_sequences_traverse(int hb,int lb, C_Polyhedron & initp);
        void dfs_sub_sequences_traverse_recursive_based_on_StInG(vector<vector<int>> & sub_sequences,int hb,int lb,int depth,C_Polyhedron & cpoly,C_Polyhedron & invd);
        void dfs_sub_sequences_traverse_recursive(vector<vector<int>> & sub_sequences,int hb,int lb,int depth,C_Polyhedron & cpoly,Clump & invd_vp);
        void collect_invariant_polys(C_Polyhedron & cpoly,Clump & invd_vp);
        void collect_sub_sequences(vector<vector<int>> & sub_sequences, int hb, int lb);
        void collect_invariant_polys_and_sub_sequences(Clump & invd_vp,vector<vector<int>> & sub_sequences,C_Polyhedron & cpoly,int hb,int lb);
        void collect_invariant_polys_and_sub_sequences(Clump & invd_vp,vector<vector<int>> & sub_sequences,C_Polyhedron & cpoly,vector<int> & sequence);
        void dfs_sequences_traverse(vector<vector<vector<int>>> sequences, C_Polyhedron & initp, C_Polyhedron & invd);
        void dfs_sequences_traverse_recursive2(vector<int> & sequence, vector<vector<vector<int>>> sequences, int i, int depth, C_Polyhedron & cpoly, C_Polyhedron & invd);
        bool has_the_same_sequences_from_the_left(vector<int> banged_s, vector<int> s);
        //void dfs_sequences_traverse_recursive(vector<int> & sequence, vector<vector<vector<int>>> sequences, int i, C_Polyhedron & initp, C_Polyhedron & invd);
        //void read_a_sequence(vector<int> sequence, C_Polyhedron & cpoly, C_Polyhedron & invd);
};

inline vector<Clump> & Tree::get_tree(){
    return vcl;
}

inline int Tree::size(){
    return vcl.size();
}

inline int Tree::get_ra(){return ra;}
inline int Tree::get_er(){return er;}
inline int Tree::get_unra(){return unra;}
inline int Tree::get_uner(){return uner;}
inline int Tree::get_target_index(){return target_index;}
inline int Tree::get_max_clump_count(){return max_clump_count;}

inline Clump & Tree::get_clump(int depth){
    return vcl[depth];
}

inline void Tree::clear_pruned_node(){
    pruned_node.clear();
}

inline int Tree::get_first_conflict(){
    return first_conflict;
}

inline void Tree::clear_first_conflict(){
    first_conflict = -1;
}

#endif