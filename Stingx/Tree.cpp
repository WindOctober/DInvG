
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


void Tree::collectInv(int index, C_Polyhedron& cpoly, C_Polyhedron& invCoefPoly) {
    invCoefPoly = C_Polyhedron(coefInfo->getDim(), UNIVERSE);
    (*locList)[index]->ExtractAndUpdateInv(cpoly, invCoefPoly);
    return;
}
int Tree::getTransIndex(string name){
    for(int i=0;transList->size();i++){
        TransitionRelation *trans=(*transList)[i];
        if (trans->getName()==name)
            return i;
    }
    return -1;
}

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

void Tree::setInfo(var_info* recInfo,var_info* recCoefInfo,var_info* recLambdaInfo){
    info=recInfo;
    coefInfo=recCoefInfo;
    lambdaInfo=recLambdaInfo;
    return;
}

void Tree::setLocTrans(vector<Location*>* recLocList,
                     vector<TransitionRelation*>* recTransList){
    locList=recLocList;
    transList=recTransList;
    return;
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

void Tree::setPriorClumps(vector<Clump>& clumps) {
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
        if (it->getCategory() == "Transition") {
            transition_index = getTransIndex(it->getName());
            transPreLocName = (*transList)[transition_index]->getPreLocName();
            transPostLocName = (*transList)[transition_index]->getPostLocName();
            if (transPreLocName == target || transPostLocName == target) {
                relatedTransId.push_back(j);
            } else {
                unrelatedTransId.push_back(j);
            }
        } else if (it->getCategory() == "Location") {
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

void Tree::setIntraClumps(vector<Clump>& clumps) {
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
        if (it->getCategory() == "Location") {
            if (it->getName() == target) {
                targetId.push_back(j);
            }
        }
        j++;
    }

    set_ra(targetId.size());
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
        cout << " --  " << getClump(dth - 1).getCategory();
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
        cout << " --  " << getClump(dth - 1).getCategory();
        if (getClump(dth - 1).getCategory() == "Location") {
            cout << "_Intra";
        } else if (getClump(dth - 1).getCategory() == "Transition") {
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
        cout << " --  " << getClump(dth - 1).getCategory();
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
        cout << " --  " << getClump(dth - 1).getCategory();
        cout << ":: " << getClump(dth - 1).getName();
        if (lb <= dth - 1 && dth - 1 <= hb) {
            i++;
        }
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

vector<vector<vector<int>>> Tree::seqGen(string divide_into_sections,
                                         C_Polyhedron& initp) {
    cout << endl << "> > > Tree::sequences generation()";

    vector<vector<vector<int>>> sequences;

    if (divide_into_sections == "one_per_group") {
        sequences = one_per_group(initp);
    } else if (divide_into_sections == "two_per_group") {
        sequences = two_per_group(initp);
    }

    cout << endl << "< < < Tree::sequences generation()";
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
        sequences.push_back(sub_sequences);
    }

    cout << endl << "< < < Tree::two_per_group()";
    return sequences;
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
    if (invd_vp.contains(poly)) {
        totalPrunedCnt++;
        return;
    }

    if (depth == lb) {
        collect_invariant_polys_and_sub_sequences(invd_vp, sub_sequences, poly,
                                                  hb, lb);

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
                           C_Polyhedron& invCoefPoly) {
    cout << endl << "> > > Tree::treeSeqTraverse()";

    int start = 0;
    vector<int> sequence;
    int depth = clumps.size() - 1;
    dfsSequences(sequence, sequences, start, depth, initp, invCoefPoly);
    cout << endl << "< < < Tree::treeSeqTraverse()";
}

void Tree::dfsSequences(vector<int>& sequence,
                        vector<vector<vector<int>>> sequences,
                        int i,
                        int depth,
                        C_Polyhedron& poly,
                        C_Polyhedron& invCoefPoly) {
    if (i == sequences.size()) {
        totalSuccessCnt++;

        cout << endl;
        cout << endl << "sequence:";
        for (int k = 0; k < sequence.size(); k++) {
            cout << sequence[k];
        }
        cout << endl << "/-----------------------------";
        collectInv(curId, poly, invCoefPoly);
        cout << endl;
        cout << endl
             << "- Have Collected " << totalSuccessCnt << " invariant(s)";
        cout << endl << "------------------------------";
        cout << endl << "- poly: " << endl << "  " << poly;
        cout << endl << "- invCoefPoly: " << endl << "  " << invCoefPoly;
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
            p.intersection_assign(getClump(depth - index).getReference(*it));
            // exit(0);
            if (invCoefPoly.contains(p)) {
                totalPrunedCnt++;
                prunedSeq = tmpSeq;
                prunedFlag = true;
                break;
            }
            index++;
        }

        if (!prunedFlag) {
            dfsSequences(printedSeq, sequences, i + 1, depth - index, p,
                         invCoefPoly);
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