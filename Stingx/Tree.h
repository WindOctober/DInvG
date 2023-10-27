
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

#include <algorithm>
#include <iostream>
#include <vector>

#include "Clump.h"
#include "Location.h"
#include "ToolUtils.h"
#include "TransitionRelation.h"
#include "ppl.hh"

using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;

class Tree {
   private:
    vector<Clump> clumps;
    void initialize(vector<Clump>& clumps);
    int ra;    // related location(intra)
    int er;    // related transition(inter)
    int unra;  // un-related location(intra)
    int uner;  // un-related transition(inter)
    int curId = -1;
    int maxPolyNum = -1;

    vector<pair<int, vector<int>>> pruned_node;
    vector<int> clumps_gli;
    vector<int> conflict_depth;
    int first_conflict = -1;

   public:
    Tree();
    Tree(vector<Clump>& clumps);
    void set_tree(vector<Clump>& clumps);
    vector<Clump>& get_tree();
    int size();
    void set_ra(int amount);
    void set_er(int amount);
    void set_unra(int amount);
    void set_uner(int amount);
    void setCurId(int index);
    void setMaxPolyNum();
    int get_ra();
    int get_er();
    int get_unra();
    int get_uner();
    int get_target_index();
    int get_max_clump_count();
    Clump& getClump(int depth);
    void Original_Prior(vector<Clump>& clumps);
    void Reorder_Target_Prior_1(vector<Clump>& clumps);
    void setPriorClumps(vector<Clump>& clumps);
    void Reorder_Target_Prior_3(vector<Clump>& clumps);
    void setIntraClumps(vector<Clump>& clumps);
    void Print_Prune_Tree(int depth, string weavedorbanged);
    void Print_Prune_Tree(int depth, int hb, int lb, string weavedorbanged);
    void Print_Prune_Sequence_Tree(vector<int> sequence,
                                   int depth,
                                   string weavedorbanged);
    void Print_Prune_Sequence_Tree(vector<int> sequence,
                                   int depth,
                                   int hb,
                                   int lb,
                                   string weavedorbanged);

    // prune method 1
    void prune_node_self_inspection(int curId, C_Polyhedron& invCoefPoly);
    void insert_pruned_node(int depth, vector<int> node_gli);
    void clear_pruned_node();
    void store_conflict_node();
    void store_clumps_gli();
    int get_first_conflict();
    void clear_first_conflict();

    // prune method 2
    void prune_clumps_by_hierarchy_inclusion();

    // treeSeqTraverse
    vector<vector<vector<int>>> seqGen(
        string divide_into_sections,
        C_Polyhedron& initp);
    vector<vector<vector<int>>> one_per_group(C_Polyhedron& initp);
    vector<vector<vector<int>>> two_per_group(C_Polyhedron& initp);
    vector<vector<vector<int>>> merge_sub_sequences(
        vector<vector<vector<int>>> sequences,
        C_Polyhedron initp);
    vector<vector<vector<int>>> merge_target_sub_sequences(
        vector<vector<vector<int>>> sequences,
        C_Polyhedron initp);
    vector<vector<vector<int>>> merge_first_sub_sequences(
        vector<vector<vector<int>>> sequences,
        C_Polyhedron initp);
    vector<vector<vector<int>>> merge_end_sub_sequences(
        vector<vector<vector<int>>> sequences,
        C_Polyhedron initp);
    vector<vector<int>> Merge(vector<vector<int>> sub_sequences1,
                              vector<vector<int>> sub_sequences2,
                              int hb,
                              int lb,
                              C_Polyhedron initp);
    void Merge_recursive2(vector<vector<vector<int>>> two_sub_sequences,
                          vector<vector<int>>& merged_sub_sequences,
                          vector<int>& sequence,
                          int i,
                          int depth,
                          C_Polyhedron& cpoly,
                          Clump& invd_vp,
                          int hb,
                          int lb);
    // void Merge_recursive(vector<vector<vector<int>>> two_sub_sequences,
    // vector<vector<int>> & merged_sub_sequences, int i, vector<int> sequence,
    // C_Polyhedron initp, Clump & invd_vp, int hb, int lb); void
    // read_and_collect_a_sequence(vector<vector<int>> & merged_sub_sequences,
    // vector<int> sequence, C_Polyhedron cpoly, Clump & invd_vp, int hb, int
    // lb);
    vector<vector<int>> dfs_sub_sequences_traverse(int hb,
                                                   int lb,
                                                   C_Polyhedron& initp);

    void dfs_sub_sequences_traverse_recursive(
        vector<vector<int>>& sub_sequences,
        int hb,
        int lb,
        int depth,
        C_Polyhedron& cpoly,
        Clump& invd_vp);
    void collect_invariant_polys(C_Polyhedron& cpoly, Clump& invd_vp);
    void collect_sub_sequences(vector<vector<int>>& sub_sequences,
                               int hb,
                               int lb);
    void collect_invariant_polys_and_sub_sequences(
        Clump& invd_vp,
        vector<vector<int>>& sub_sequences,
        C_Polyhedron& cpoly,
        int hb,
        int lb);
    void collect_invariant_polys_and_sub_sequences(
        Clump& invd_vp,
        vector<vector<int>>& sub_sequences,
        C_Polyhedron& cpoly,
        vector<int>& sequence);
    void treeSeqTraverse(vector<vector<vector<int>>> sequences,
                                C_Polyhedron& initp,
                                C_Polyhedron& invCoefPoly);
    void dfsSequences(
        vector<int>& sequence,
        vector<vector<vector<int>>> sequences,
        int i,
        int depth,
        C_Polyhedron& cpoly,
        C_Polyhedron& invCoefPoly);
    bool checkSeqPrefix(vector<int> prunedSeq,
                                              vector<int> s);
};

inline vector<Clump>& Tree::get_tree() {
    return clumps;
}

inline int Tree::size() {
    return clumps.size();
}

inline int Tree::get_ra() {
    return ra;
}
inline int Tree::get_er() {
    return er;
}
inline int Tree::get_unra() {
    return unra;
}
inline int Tree::get_uner() {
    return uner;
}
inline int Tree::get_target_index() {
    return curId;
}
inline int Tree::get_max_clump_count() {
    return maxPolyNum;
}

inline Clump& Tree::getClump(int depth) {
    return clumps[depth];
}

inline void Tree::clear_pruned_node() {
    pruned_node.clear();
}

inline int Tree::get_first_conflict() {
    return first_conflict;
}

inline void Tree::clear_first_conflict() {
    first_conflict = -1;
}

#endif