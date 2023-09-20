// DONE: return the final disjunctive invariant to the Frontend.
#include <iostream>
#include <regex>
#include <string>
#include <vector>
#include "Elimination.h"
#include "Location.h"
#include "PolyUtils.h"
#include "Propagation.h"
#include "System.h"
#include "Timer.h"
#include "TransitionRelation.h"
#include "Tree.h"
#include "ppl.hh"
#include "var-info.h"
using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;
bool gendrop;
bool print_tree;
bool zero;
bool one;
bool falsepath;
bool noexitpath;
bool djinv;
bool arrinv;
int prop_steps;
int time_limit;
int total_time;
string projection;
string tree_prior;
string some_per_group;
bool clear_lower_gli = false;
int clear_lower_gli_depth = -1;
bool backhere_flag = false;
int related_location_number;
int related_transition_number;

C_Polyhedron *trivial, *dualp;

#ifndef MAX_ID_SIZE
#define MAX_ID_SIZE 100
#endif

#define DEBUG 1001
#define DEBUG_2 1002
#define DEBUG_3 1003
#define NO_PRINT_TREE 1010
#define ONECONTEXT 0
#define GENDROP 1
#define MANYCONTEXT 2
#define BULLSHIT 3
#define NEW_MANYCONTEXT 401
#define NEW_2_MANYCONTEXT 402
#define NEW_3_MANYCONTEXT 403
#define NEWDFS 404
#define NEWDFS_SEQUENCES 405
#define NEWDFS_SEQ_PROPAGATION 406
#define NO_PROJECTION 410
#define KOHLER_ELIMINATE_C 411
#define FARKAS_ELIMINATE_C 412
#define FOUMOT_ELIMINATE_C 413
#define NO_PRIOR 420
#define TARGET_PRIOR1 421
#define TARGET_PRIOR2 422
#define TARGET_PRIOR3 423
#define ONE_PER_GROUP 431
#define TWO_PER_GROUP 432
#define THREE_PER_GROUP 433
#define FOUR_PER_GROUP 434
#define ZERO_ONLY 501
#define ONE_ONLY 502
#define ZERO_ONE 503
#define YES_FALSEPATH 511
#define NO_FALSEPATH 512
#define YES_TRSAT 513
#define NO_TRSAT 514
#define YES_EXITPATH 521
#define NO_EXITPATH 522
#define YES_DJINV 601
#define NO_DJINV 602
#define YES_ARRINV 611
#define NO_ARRINV 612
#define NO_INSTANTIATION 8
#define INV_CHECK 15
#define NO_INV_CHECK 16
vector<int>** location_matrix;
int global_binary_i = 0;
long int global_contains_time = 0;
vector<int> target_prior;

char err_str[100];
extern int linenum;
int dimension;
var_info *info, *coefInfo, *lambdaInfo;
vector<Location*>* loclist;
vector<TransitionRelation*>* transList;
Context* glc;  // The global context
vector<Context*>* children;
vector<System*>* global_sub_system_list;
System* globalSys;
Timer total_timer;
Timer weave_timer;
Timer dfs_traverse_timer;
Timer single_dfs_traverse_timer;
Timer collect_timer;
Timer prune_nodes_timer;
Timer backtrack_timer;
Timer single_dfs_sequences_generation_timer;
Timer single_dfs_sequences_traverse_timer;
Timer single_merge_sub_sequences_timer;
long int dfs_traverse_time;
int collect_time = 0;
int prune_nodes_time = 0;
int backtrack_time = 0;
vector<int> vector_single_collect_time;
vector<int> vector_single_dfs_traverse_time;
vector<int> vector_single_dfs_sequences_generation_time;
vector<int> vector_single_dfs_sequences_traverse_time;
int single_collect_time;
int* tt;
C_Polyhedron* invd;

bool inv_check;

void collect_generators(vector<Context*>* children, Generator_System& g);
int single_weave_count;
vector<int> vector_single_weave_count;
int weave_count;
int single_bang_count;
vector<int> vector_single_bang_count;
int single_pre_prune_bang_count;
int single_post_prune_bang_count;
vector<int> vector_single_pre_prune_bang_count;
vector<int> vector_single_post_prune_bang_count;
int bang_count;
int backtrack_count;
int backtrack_success;
bool backtrack_flag;
int prune_count;
int clump_prune_count;
int context_count;
int merge_count;
int bang_count_in_merge;
Counter counter;
bool searchLoc(char* w, Location** m);
bool searchTransRel(char* w, TransitionRelation** m);
void addPreInvtoTrans();
void print_status();

void check_invariant_ok();
void ScanInput();

bool searchLoc(char* name, Location** what) {
    vector<Location*>::iterator it;
    string nstr(name);
    for (it = loclist->begin(); it < loclist->end(); it++) {
        if ((*it)->matches(nstr)) {
            *what = (*it);
            return true;
        }
    }

    return false;
}

bool searchTransRel(char* name, TransitionRelation** what) {
    vector<TransitionRelation*>::iterator it;
    string nstr(name);
    for (it = transList->begin(); it < transList->end(); it++) {
        if ((*it)->matches(nstr)) {
            *what = (*it);
            return true;
        }
    }

    return false;
}
void PrintLocs();
void collect_invariants(C_Polyhedron& cpoly, C_Polyhedron& invd) {
    invd = C_Polyhedron(coefInfo->getDim(), UNIVERSE);
    for (auto it = loclist->begin(); it < loclist->end(); it++) {
        (*it)->extract_invariants_and_update(cpoly, invd);
    }
    return;
}

void collect_invariants_for_one_location_by_eliminating(int index,
                                                        C_Polyhedron& cpoly,
                                                        C_Polyhedron& invd) {
    //
    //  Collect invariants for initial
    //
    invd = C_Polyhedron(coefInfo->getDim(), UNIVERSE);
    //    Firstly, collect invariants for initial location by eliminating
    //      for initial *it, i.e. location,
    //      use cpoly to update *it->invariant and *it->invariant updates invd.
    (*loclist)[index]
        ->extract_invariants_and_update_for_one_location_by_eliminating(cpoly,
                                                                        invd);

    return;
}

void dfs_sequences_generation_traverse(
    vector<vector<vector<vector<int>>>>& target_sequences,
    int index,
    vector<Clump>& clumps,
    C_Polyhedron& initPoly) {
    Tree tr = Tree();
    tr.set_target_index(index);

    for (auto it = clumps.begin(); it < clumps.end(); it++) {
        (*it).clear();
    }

    cout << endl
         << endl
         << "/ Start to solve Location " << (*loclist)[index]->getName();
    if (tree_prior == "no_prior") {
        cout << endl << "/ Using no_prior";
        tr.Original_Prior(clumps);
    } else if (tree_prior == "target_prior1") {
        cout << endl << "/ Using target_prior1";
        tr.Reorder_Target_Prior_1(clumps);
    } else if (tree_prior == "target_prior2") {
        cout << endl << "/ Using target_prior2";    
        tr.Reorder_Target_Prior_2(clumps);
    } else if (tree_prior == "target_prior3") {
        cout << endl << "/ Using target_prior3";
        tr.Reorder_Target_Prior_3(clumps);
    } else {
        cout << endl << "Wrong Type: " << tree_prior;
    }

    tr.set_max_clump_count();

    cout << endl << "/ Generate Sequences";
    vector<vector<vector<int>>> sequences;
    sequences = tr.sequences_generation(some_per_group, initPoly);
    target_sequences.push_back(sequences);
}

void dfs_sequences_generation_traverse_for_one_location_from_intra(
    vector<vector<vector<vector<int>>>>& target_sequences,
    int index,
    vector<Clump>& clumps,
    C_Polyhedron& initPoly) {
    // C_Polyhedron invd(*trivial);
    Tree tr = Tree();  // empty tree
    tr.set_target_index(index);
    vector<Clump>::iterator it;
    for (it = clumps.begin(); it < clumps.end(); it++) {
        (*it).clear();  
    }

    cout << endl
         << endl
         << "/ Start to solve Location " << (*loclist)[index]->getName();
    // extract only-one-clumps which is intra-transition about this location
    tr.extract_vcl_for_one_location_about_intra(clumps);

    tr.set_max_clump_count();

    cout << endl << "/ Generate Sequences";
    vector<vector<vector<int>>> sequences;
    sequences = tr.sequences_generation("one_per_group", initPoly);
    target_sequences.push_back(sequences);

    cout << endl << "\\ Generate Sequences";
    cout << endl
         << "\\ End to solve Location " << (*loclist)[index]->getName();
}

void dfs_sequences_traverse_for_one_location_by_eliminating(
    vector<vector<vector<int>>> sequences,
    int index,
    vector<Clump>& clumps,
    C_Polyhedron& initPoly) {
    C_Polyhedron invd(*trivial);
    Tree tr = Tree();  // empty tree
    tr.set_target_index(index);
    // int clumpsNum=0;
    vector<Clump>::iterator it;
    for (it = clumps.begin(); it < clumps.end(); it++) {
        // clumpsNum++;
        (*it).clear();
    }

    cout << endl
         << endl
         << "/ Start to solve Location " << (*loclist)[index]->getName();
    if (tree_prior == "no_prior") {
        cout << endl << "/ Using no_prior";
        tr.Original_Prior(clumps);
    } else if (tree_prior == "target_prior1") {
        cout << endl << "/ Using target_prior1";
        tr.Reorder_Target_Prior_1(clumps);
    } else if (tree_prior == "target_prior2") {
        cout << endl << "/ Using target_prior2";
        tr.Reorder_Target_Prior_2(clumps);
    } else if (tree_prior == "target_prior3") {
        cout << endl << "/ Using target_prior3";
        tr.Reorder_Target_Prior_3(clumps);
    } else {
        cout << endl << "Wrong Type: " << tree_prior;
    }

    tr.set_max_clump_count();
    // tr.prune_clumps_by_hierarchy_inclusion();
    // cout<<endl;
    cout << endl << "/ Read(Traverse) Sequences";
    tr.dfs_sequences_traverse(sequences, initPoly, invd);
}

void dfs_sequences_traverse_for_one_location_from_intra_by_eliminating(
    vector<vector<vector<int>>> sequences,
    int index,
    vector<Clump>& clumps,
    C_Polyhedron& initPoly) {
    C_Polyhedron invd(*trivial);
    Tree tr = Tree();  // empty tree
    tr.set_target_index(index);
    vector<Clump>::iterator it;
    for (it = clumps.begin(); it < clumps.end(); it++) {
        (*it).clear();
    }

    cout << endl
         << endl
         << "/ Start to solve Location " << (*loclist)[index]->getName();
    // extract only-one-clumps which is intra-transition about this location
    tr.extract_vcl_for_one_location_about_intra(clumps);

    tr.set_max_clump_count();

    cout << endl << "/ Read(Traverse) Sequences";
    tr.dfs_sequences_traverse(sequences, initPoly, invd);

    cout << endl << "\\ Read(Traverse) Sequences";
    cout << endl
         << "\\ End to solve Location " << (*loclist)[index]->getName();
}

// compute invariants by farkas for this one location from intra-transition
void collect_invariants_for_one_location_from_intra(vector<Clump>& clumps,
                                                    int loc_index) {
    // initialize
    int lid = loc_index;
    vector<vector<vector<vector<int>>>> target_sequences;
    int coefNum = coefInfo->getDim();
    C_Polyhedron local_initp(coefNum, UNIVERSE);

    /*
     * Generate Sequences
     */
    single_pre_prune_bang_count = 0;
    counter.set_location_index_and_init_depth(lid, clumps.size());
    // compute invariants by using initial-value and intra-transition
    bool has_initial_polyset = (*loclist)[lid]->isInitLoc();
    if (!has_initial_polyset) {
        cout << endl
             << "- ( !has_initial_polyset ) in Location::"
             << (*loclist)[lid]->getName();
        vector<vector<vector<int>>> empty_sequences;
        target_sequences.push_back(empty_sequences);
    } else {
        (*loclist)[lid]->ComputeDualConstraints(local_initp);
        dfs_sequences_generation_traverse_for_one_location_from_intra(
            target_sequences, lid, clumps, local_initp);
    }

    /*
     * Read Sequences
     */
    single_weave_count = 0;
    single_collect_time = 0;
    single_post_prune_bang_count = 0;
    // compute invariants by using initial-value and intra-transition
    if (!has_initial_polyset) {
        cout << endl
             << "- ( !has_initial_polyset ) in Location::"
             << (*loclist)[lid]->getName();
    } else {
        vector<vector<vector<int>>> sequences;
        if (target_sequences.size() == 1) {
            sequences = target_sequences[0];
        } else {
            cout << endl << "Error: There are more than one sequences";
        }
        dfs_sequences_traverse_for_one_location_from_intra_by_eliminating(
            sequences, lid, clumps, local_initp);
    }

    return;
}

void Initialize_before_Parser() {
    cout << endl << "- Initialize_before_Parser doing...";
    weave_count = bang_count = backtrack_count = 0;
    backtrack_success = 0;
    backtrack_flag = false;
    merge_count = 0;
    inv_check = false;
    clump_prune_count = prune_count = 0;
    context_count = 0;
    lambdaInfo = new var_info();
    coefInfo = new var_info();
    loclist = new vector<Location*>();
    transList = new vector<TransitionRelation*>();
    print_tree = true;
    projection = "kohler_improvement_eliminate_c";
    tree_prior = "target_prior2";
    some_per_group = "two_per_group";
    gendrop = false;
    global_sub_system_list = new vector<System*>();
    zero = one = true;
    falsepath = true;
    noexitpath = true;
    djinv = true;
    arrinv = false;
    prop_steps = 2;
    time_limit = 360000;
    total_time = 360000;
    cout << "Done!" << endl;
}

void Initialize() {
    cout << endl << "- Initialize_before_Parser doing...";
    weave_count = bang_count = backtrack_count = 0;
    backtrack_success = 0;
    backtrack_flag = false;
    merge_count = 0;
    inv_check = false;
    clump_prune_count = prune_count = 0;
    context_count = 0;
    print_tree = true;
    projection = "kohler_improvement_eliminate_c";
    tree_prior = "target_prior2";
    some_per_group = "two_per_group";
    gendrop = false;
    global_sub_system_list = new vector<System*>();
    zero = one = true;
    falsepath = true;

    noexitpath = true;
    djinv = true;
    arrinv = false;
    prop_steps = 2;
    time_limit = 360000;
    total_time = 360000;
}

void PrintLocsTrans() {
    cout << endl;
    cout << "----------------------------- " << endl;
    cout << "| The Locations read in are: " << endl;
    cout << "----------------------------- " << endl;
    for (vector<Location*>::iterator it = loclist->begin(); it < loclist->end();
         it++) {
        cout << *(*it);
    }
    cout << "----------------------------- " << endl;
    cout << "| The Transitions read in are: " << endl;
    cout << "----------------------------- " << endl;
    for (vector<TransitionRelation*>::iterator it = transList->begin();
         it < transList->end(); it++) {
        cout << *(*it);
    }
}

void PrintLocs() {
    cout << endl;
    cout << "----------------------------- " << endl;
    cout << "| The Locations read in are: " << endl;
    cout << "----------------------------- " << endl;
    for (vector<Location*>::iterator it = loclist->begin(); it < loclist->end();
         it++) {
        cout << *(*it);
    }
}

void PrintInvInExitLoc() {
    cout << endl << "/---------------------------------------- ";
    cout << endl << "| Disjunctive Invariants before Program: ";
    cout << endl << "----------------------------------------- ";
    int i = 0;
    for (vector<Location*>::iterator it = loclist->begin(); it < loclist->end();
         it++) {
        if ((*it)->getName() != EXIT_LOCATION &&
            !(*it)->GetInv().is_empty()) {
            if (i != 0) {
                cout << endl << "\\/";
            }
            print_pure_polyhedron((*it)->GetInv(),
                                  (*it)->getInfo());
            i++;
        }
    }
    cout << endl << "\\---------------------------------------- ";
    cout << endl;
}

void PrintStatusBeforeSolving() {
    cout << endl;
    cout << "/----------------------------- " << endl;
    cout << "| Status before Solver: " << endl;
    cout << "----------------------------- " << endl;
    cout << "| Print Tree : " << print_tree << endl;
    cout << "| DFS Search method : " << tree_prior << endl;
    cout << "| Sequences Divide method : " << some_per_group << endl;
    cout << "| Projection method : " << projection << endl;
    cout << "| Local invariants to be generated : " << zero << endl;
    cout << "| Increasing invariants to be generated : " << one << endl;
    cout << "| Falsepath to be enabled : " << falsepath << endl;
    cout << "| Exit-Transition is computed : " << (!noexitpath) << endl;
    cout << "| Display Disjunctive Invariants : " << djinv << endl;
    cout << "| Display Array Invariants : " << arrinv << endl;
    cout << "| Weave time allowed : " << time_limit << endl;
    cout << "\\----------------------------- " << endl;
}

void Print_Status_after_Solver() {
    cout << endl;
    cout << "/----------------------------- " << endl;
    cout << "| Status after Solver: " << endl;
    cout << "----------------------------- " << endl;
    cout << "| Time Taken Unit: (0.01s)" << endl;
    cout << "| # of Contexts generated = " << context_count << endl;
    cout << "|" << endl;

    cout << "| # of pruned clumps in intra-transition = " << prune_count << endl;
    cout << "| # of pruned nodes by self inspection = " << clump_prune_count
         << ", Time = " << prune_nodes_time << endl;
    cout << "| # of pruned by backtracking = " << backtrack_count
         << ", Time = " << backtrack_time << endl;
    cout << "| # of merged for sub sequences = " << merge_count << endl;
    cout << "|" << endl;

    cout << "| t: collect_invariant Time" << endl;
    cout << "| w: invariants *weav*ed" << endl;
    for (vector<int>::size_type i = 0; i < vector_single_collect_time.size();
         ++i) {
        cout << "| LOC " << i << ": t = " << vector_single_collect_time[i]
             << ", w = " << vector_single_weave_count[i] << endl;
    }
    cout << "| TOTAL: t = " << collect_time << ", w = " << weave_count << endl;
    cout << "|" << endl;

    cout << "| t: dfs_traverse Time" << endl;
    cout << "| b: path *bang*ed" << endl;
    /*
        * Following record message for "newdfs" (i.e., without
        * divide_into_group):
        *   LOC,
        *   vector_single_bang_count
        */
    for (vector<int>::size_type i = 0;
            i < vector_single_dfs_traverse_time.size(); ++i) {
        cout << "| LOC_" << i
                << ": t = " << vector_single_dfs_traverse_time[i]
                << ", b = " << vector_single_bang_count[i] << endl;
    }
    /*
        * Following record message for "newdfs_sequences" (i.e., without
        * divide_into_group):
        *   PRE,
        *   vector_single_pre_prune_bang_count,
        *   PST,
        *   vector_single_post_prune_bang_count
        */
    for (vector<int>::size_type i = 0;
            i < vector_single_pre_prune_bang_count.size(); ++i) {
        cout << "| PRE_" << i
                << ": t = " << vector_single_dfs_sequences_generation_time[i]
                << ", b = " << vector_single_pre_prune_bang_count[i] << endl;
    }
    for (vector<int>::size_type i = 0;
            i < vector_single_post_prune_bang_count.size(); ++i) {
        cout << "| PST_" << i
                << ": t = " << vector_single_dfs_sequences_traverse_time[i]
                << ", b = " << vector_single_post_prune_bang_count[i] << endl;
    }
    cout << "| TOTAL: t = " << dfs_traverse_time << ", b = " << bang_count
            << endl;
    cout << "|" << endl;

    cout << "| TOTAL Time = " << total_timer.getElapsedTime() << endl;
    cout << "\\----------------------------- " << endl;
}

int getLocIndex(string locName) {
    int i = 0;
    for (vector<Location*>::iterator it = loclist->begin(); it < loclist->end();
         it++) {
        if ((*it)->getName() == locName) {
            return i;
        }
        i++;
    }
    return -1;
}

int getTransIndex(string name) {
    int i = 0;
    for (vector<TransitionRelation*>::iterator it = transList->begin();
         it < transList->end(); it++) {
        if ((*it)->getName() == name) {
            return i;
        }
        i++;
    }
    return -1;
}


// return the transition-index
// which is start from this pre-location-index except intra-transition
// and except someother transition-index
vector<int> get_intertid_from_prelid_without_some(int prelid, string some) {
    vector<int> tid;
    int size = transList->size();

    for (int ti = 0; ti < size; ti++) {
        if ((*transList)[ti]->get_preloc_index() == prelid &&
            (*transList)[ti]->get_postloc_index() != prelid &&
            (*transList)[ti]->getPostLocName() != some) {
            tid.push_back(ti);
        }
    }

    return tid;
}

// return the inter-transition-index which is end at this post-location-index
vector<int> get_intertid_to_postlid(int postlid) {
    vector<int> tid;
    int size = transList->size();

    for (int ti = 0; ti < size; ti++) {
        if ((*transList)[ti]->get_postloc_index() == postlid &&
            (*transList)[ti]->get_preloc_index() != postlid) {
            tid.push_back(ti);
        }
    }

    return tid;
}

void CreateAdjMat() {
    int loclist_size = loclist->size();
    location_matrix = new vector<int>*[loclist_size];
    for (int i = 0; i < loclist_size; i++) {
        location_matrix[i] = new vector<int>[loclist_size];
    }

    int j = 0, j1 = 0;
    for (auto it = transList->begin(); it < transList->end(); it++) {
        if (!(*it)->getTransRel().is_empty()) {
            location_matrix[getLocIndex((*it)->getPreLocName())]
                            [getLocIndex(
                                (*it)->getPostLocName())]
                                .push_back(j);
            j1++;
        }
        j++;

    }

    //  print the matrix
    cout << endl << "/----------------------------- ";
    cout << endl << "| Adjacency Matrix for Location and Transition: ";
    cout << endl << "----------------------------- ";
    cout << endl << "| Input: " << transList->size() << " transitions";
    cout << endl << "----------------------------- ";
    cout << endl << "| [#] is transition_index";
    for (int i = 0; i < loclist_size; i++) {
        cout << endl << "| " << (*loclist)[i]->getName() << ": ";
        for (int j = 0; j < loclist_size; j++) {
            cout << "[";
            for (vector<int>::iterator it = location_matrix[i][j].begin();
                 it < location_matrix[i][j].end(); it++) {
                cout << " " << *it << " ";
            }
            cout << "]->" << (*loclist)[j]->getName() << ";  ";
        }
    }
    cout << endl << "----------------------------- ";
    cout << endl << "| Output: " << j1 << " transitions";
    cout << endl << "\\----------------------------- ";
}

void Clear_Location_Invariant() {
    for (auto it = loclist->begin(); it < loclist->end(); it++) {
        cout << endl
             << "- Location " << (*it)->getName() << ": initialize invariant";
        (*it)->initialize_invariant();
    }
}

void Compute_Invariant_Frontend(){
    total_timer.restart();
    Initialize();
    addPreInvtoTrans();
    CreateAdjMat();
    globalSys = new System(info, coefInfo, lambdaInfo);

    for (auto it = loclist->begin(); it < loclist->end(); it++) {
        globalSys->addLoc((*it));
    }
    for (auto it = transList->begin(); it < transList->end(); it++) {
        globalSys->addTrans((*it));
    }
    tt = new int[lambdaInfo->getDim()];
    int coefNum = coefInfo->getDim();
    trivial = new C_Polyhedron(coefNum, UNIVERSE);
    for (auto it = loclist->begin(); it < loclist->end(); it++) {
        (*it)->addTrivial(trivial);
    }

    C_Polyhedron initPoly(coefNum, UNIVERSE);
    for (auto it = loclist->begin(); it < loclist->end(); it++) {
        (*it)->makeContext();
        (*it)->ComputeDualConstraints(initPoly);
    }
    vector<Clump> clumps;
    for (auto it = transList->begin(); it < transList->end(); it++) {
        (*it)->ComputeIntraConsecConstraints(clumps);
        if (total_timer.getElapsedTime() >= time_limit) {
            cout << "Time is up!" << endl;
            break;
        }
    }

    for (auto it = loclist->begin(); it < loclist->end(); it++) {
        (*it)->addClump(clumps);
        if (total_timer.getElapsedTime() >= time_limit) {
            cout << "Time is up!" << endl;
            break;
        }
    }

    dfs_traverse_timer.restart();
    vector<vector<vector<vector<int>>>> target_sequences;
    for (int index = 0; index < loclist->size(); index++) {
        single_pre_prune_bang_count = 0;
        counter.set_location_index_and_init_depth(index, clumps.size());
        single_dfs_sequences_generation_timer.restart();

        // only compute invariants at initial location
        bool initLocFlag = (*loclist)[index]->getInitFlag();
        if (!initLocFlag) {
            cout << endl
                    << "- ( !initLocFlag ) in Location::"
                    << (*loclist)[index]->getName();
            vector<vector<vector<int>>> empty_sequences;
            target_sequences.push_back(empty_sequences);
        } else {
            dfs_sequences_generation_traverse(target_sequences, index,
                                                clumps, initPoly);
        }

        single_dfs_sequences_generation_timer.stop();
        vector_single_dfs_sequences_generation_time.push_back(
            single_dfs_sequences_generation_timer.getElapsedTime());
        vector_single_pre_prune_bang_count.push_back(
            single_pre_prune_bang_count);
    }
    // Read Sequences
    for (int index = 0; index < loclist->size(); index++) {
        single_weave_count = 0;
        single_collect_time = 0;
        single_post_prune_bang_count = 0;
        single_dfs_sequences_traverse_timer.restart();

        // only compute invariants at initial location
        bool initLocFlag = (*loclist)[index]->getInitFlag();
        if (!initLocFlag) {
            cout << endl
                    << "- ( !initLocFlag ) in Location::"
                    << (*loclist)[index]->getName();
        } else {
            vector<vector<vector<int>>> sequences = target_sequences[index];
            dfs_sequences_traverse_for_one_location_by_eliminating(
                sequences, index, clumps, initPoly);
        }

        single_dfs_sequences_traverse_timer.stop();
        vector_single_dfs_sequences_traverse_time.push_back(
            single_dfs_sequences_traverse_timer.getElapsedTime());
        vector_single_weave_count.push_back(single_weave_count);
        vector_single_collect_time.push_back(single_collect_time);
        vector_single_post_prune_bang_count.push_back(
            single_post_prune_bang_count);
    }
    dfs_traverse_timer.stop();
    dfs_traverse_time = dfs_traverse_timer.getElapsedTime();

    compute_invariants_by_propagation_with_farkas(clumps);
    PrintLocs();
    delete tt;
    delete globalSys;
    delete trivial;
    delete location_matrix;
    return;
}
#ifdef USE_LSTINGX_MAIN
int main() {
    ios::sync_with_stdio(false);
    total_timer.restart();
    Initialize_before_Parser();
    ScanInput();
    addPreInvtoTrans();
    
    PrintStatusBeforeSolving();
    PrintLocsTrans();
    CreateAdjMat();

    globalSys = new System(info, coefInfo, lambdaInfo);
    
    for (auto it = loclist->begin(); it < loclist->end(); it++) {
        globalSys->addLoc((*it));
    }
    for (auto it = transList->begin(); it < transList->end(); it++) {
        globalSys->addTrans((*it));
    }
    tt = new int[lambdaInfo->getDim()];
    int coefNum = coefInfo->getDim();
    trivial = new C_Polyhedron(coefNum, UNIVERSE);
    for (auto it = loclist->begin(); it < loclist->end(); it++) {
        (*it)->addTrivial(trivial);
    }

    C_Polyhedron initPoly(coefNum, UNIVERSE);
    for (auto it = loclist->begin(); it < loclist->end(); it++) {
        (*it)->makeContext();
        (*it)->ComputeDualConstraints(initPoly);
    }
    vector<Clump> clumps;
    for (auto it = transList->begin(); it < transList->end(); it++) {
        (*it)->ComputeIntraConsecConstraints(clumps);
        if (total_timer.getElapsedTime() >= time_limit) {
            cout << "Time is up!" << endl;
            break;
        }
    }

    for (auto it = loclist->begin(); it < loclist->end(); it++) {
        (*it)->addClump(clumps);
        if (total_timer.getElapsedTime() >= time_limit) {
            cout << "Time is up!" << endl;
            break;
        }
    }

    // Generate Sequences
    dfs_traverse_timer.restart();
    vector<vector<vector<vector<int>>>> target_sequences;
    for (int index = 0; index < loclist->size(); index++) {
        single_pre_prune_bang_count = 0;
        counter.set_location_index_and_init_depth(index, clumps.size());
        single_dfs_sequences_generation_timer.restart();

        // only compute invariants at initial location
        bool initLocFlag = (*loclist)[index]->getInitFlag();
        if (!initLocFlag) {
            cout << endl
                    << "- ( !initLocFlag ) in Location::"
                    << (*loclist)[index]->getName();
            vector<vector<vector<int>>> empty_sequences;
            target_sequences.push_back(empty_sequences);
        } else {
            dfs_sequences_generation_traverse(target_sequences, index,
                                                clumps, initPoly);
        }

        single_dfs_sequences_generation_timer.stop();
        vector_single_dfs_sequences_generation_time.push_back(
            single_dfs_sequences_generation_timer.getElapsedTime());
        vector_single_pre_prune_bang_count.push_back(
            single_pre_prune_bang_count);
    }
    // Read Sequences
    for (int index = 0; index < loclist->size(); index++) {
        single_weave_count = 0;
        single_collect_time = 0;
        single_post_prune_bang_count = 0;
        single_dfs_sequences_traverse_timer.restart();

        // only compute invariants at initial location
        bool initLocFlag = (*loclist)[index]->getInitFlag();
        if (!initLocFlag) {
            cout << endl
                    << "- ( !initLocFlag ) in Location::"
                    << (*loclist)[index]->getName();
        } else {
            vector<vector<vector<int>>> sequences = target_sequences[index];
            dfs_sequences_traverse_for_one_location_by_eliminating(
                sequences, index, clumps, initPoly);
        }

        single_dfs_sequences_traverse_timer.stop();
        vector_single_dfs_sequences_traverse_time.push_back(
            single_dfs_sequences_traverse_timer.getElapsedTime());
        vector_single_weave_count.push_back(single_weave_count);
        vector_single_collect_time.push_back(single_collect_time);
        vector_single_post_prune_bang_count.push_back(
            single_post_prune_bang_count);
    }
    dfs_traverse_timer.stop();
    dfs_traverse_time = dfs_traverse_timer.getElapsedTime();

    /*
        * The main body of Propagation
        */

    // Test1: propagate invariants from initial location to all others
    // propagate_invariants_from_initial_location_to_all_others();

    // compute other invariants by propagation with Farkas
    // ::First, compute other location except Initial & Exit-Location
    // ::Second, compute Exit-Location
    compute_invariants_by_propagation_with_farkas(clumps);
    total_timer.stop();
    PrintLocs();
    if (djinv) {
        PrintInvInExitLoc();
    }
    Print_Status_after_Solver();
    if (inv_check) {
        check_invariant_ok();
    }

    return 0;
}
#endif
void collect_generators(vector<Context*>* children, Generator_System& g) {
    vector<Context*>::iterator vk;
    for (vk = children->begin(); vk < children->end(); vk++) {
        (*vk)->collect_generators(g);
    }
}

void addPreInvtoTrans() {
    vector<TransitionRelation*>::iterator it;
    for (it = transList->begin(); it < transList->end(); ++it) {
        (*it)->addPreInv();
    }
    return;
}

void print_status() {
    cout << "---------------------------------------------------" << endl;
    cout << " Local invariants to be generated : " << zero << endl;
    cout << " Increasing invariants to be generated : " << one << endl;
    cout << " # of initial propagation steps:" << prop_steps << endl;
    cout << " Weave Time allowed:" << time_limit << endl;
    cout << "----------------------------------------------------" << endl;
}

void check_invariant_ok() {
    cout << endl << "> > > In check_invariant_ok()";
    cerr << "Checking for invariant..." << endl;
    vector<TransitionRelation*>::iterator it;
    for (it = transList->begin(); it != transList->end(); ++it) {
        (*it)->check_map();
    }
    cerr << "Done!" << endl;
    cout << endl << "< < < Out of check_invariant_ok()";
}

void ScanInput() {
    cout << endl << "- Parsing Input Doing...";

    cout << endl << "Get Input Variable...\n";
    smatch match;
    string line;
    int stage = -1;  // Variable Reading.
    info = new var_info();
    regex trans_pattern(
        R"((Transition|transition)\s+(\w+):\s*(\w+)\s*,\s*(\w+)\s*,\s*)");
    regex self_trans_pattern(
        R"((Transition|transition)\s+(\w+)\s*:\s*(\w+)\s*,\s*)");
    regex loc_pattern(R"((Location|location)\s+(\w+)\s*)");
    regex invariant_pattern(R"((Invariant|invariant)\s+(\w+)\s*:?\s*)");
    regex term_pattern(
        R"(\s*\d+\s*\*\s*\w+\s*|\s*\d+\s*\*\s*'\w+\s*|\s*'\w+\s*|\s*\w+\s*|\s*\d+\s*|\s*|[+-]|(<=|=|>=))");
    regex primed_coef_var_pattern(R"(\s*(\d+)\s*\*\s*'(\w+)\s*)");
    regex coef_var_pattern(R"(\s*(\d+)\s*\*\s*(\w+)\s*)");
    regex primed_pattern(R"(\s*'(\w+)\s*)");
    regex var_pattern(R"(\s*(\w+)\s*)");
    regex coef_pattern(R"(\s*(\d+)\s*)");
    regex sign_pattern(R"(\s*([+-])\s*)");
    regex equality_pattern(R"(\s*(<=|=|>=)\s*)");
    regex empty_pattern(R"(\s*)");
    Location* new_location = NULL;
    Location* invariant_location = NULL;
    C_Polyhedron* new_poly = NULL;
    TransitionRelation* new_transition = NULL;
    while (getline(cin, line)) {
        istringstream iss(line);
        if (line.length() == 0)
            continue;
        string token;
        if (stage == -1 || stage == 0) {
            while (iss >> token) {
                if (token == "variable" || token == "Variable") {
                    stage = 0;
                    continue;
                } else if (stage == -1) {
                    cout << "[warning] Must Start by variable or Varible."
                         << endl;
                    exit(1);
                }
                if (token == "[") {
                    if (stage == -1) {
                        cout << "[warning] Missing variable, program execution "
                                "aborted."
                             << endl;
                        exit(1);
                    } else {
                        continue;
                    }
                }
                if (token == "]") {
                    if (stage == 0) {
                        stage = 1;
                        break;
                    } else {
                        cout << "[warning] Variable stage is ending, program "
                                "execution aborted."
                             << endl;
                        exit(1);
                    }
                }
                // cout<<token<<endl;
                info->search_and_insert(token.c_str());
            }
            continue;
        }
        if (stage == 1 || stage == 2) {
            if (line.find("end") != string::npos) {
                if (new_transition && new_poly) {
                    new_transition->set_relation(new_poly);
                }
                return;
            }
            if (regex_match(line, match, loc_pattern)) {
                if (new_poly && new_location) {
                    new_location->setPoly(new_poly);
                }
                if (new_poly && new_transition) {
                    new_transition->set_relation(new_poly);
                }
                if (new_poly && invariant_location) {
                    invariant_location->set_invariant_polyhedron(new_poly);
                }
                new_poly = NULL;
                new_location = NULL;
                invariant_location = NULL;
                new_transition = NULL;
                string locName = match[2];
                // cout<<locName<<" "<<locName.length()<<" "<<token<<endl;
                if (!searchLoc((char*)locName.c_str(), &new_location)) {
                    new_location =
                        new Location(info->getDim(), info, coefInfo,
                                     lambdaInfo, locName);
                    loclist->push_back(new_location);
                } else {
                    cerr << "[ERROR] Multi-defined Location." << endl;
                    exit(1);
                }
            } else if (regex_match(line, match, trans_pattern) ||
                       regex_match(line, match, self_trans_pattern)) {
                stage = 2;
                if (new_poly && new_location) {
                    new_location->setPoly(new_poly);
                }
                if (new_poly && new_transition) {
                    new_transition->set_relation(new_poly); }
                if (new_poly && invariant_location) {
                    invariant_location->set_invariant_polyhedron(new_poly);
                }
                new_poly = NULL;
                new_location = NULL;
                invariant_location = NULL;
                new_transition = NULL;
                string transition_name = match[2];
                string loc_name_start = match[3];
                Location* loc_end;
                Location* loc_start;
                // cout<<endl;
                if (!searchTransRel((char*)transition_name.c_str(),
                                                &new_transition)) {
                    new_transition = new TransitionRelation(
                        info->getDim(), info, coefInfo, lambdaInfo,
                        transition_name);
                    transList->push_back(new_transition);
                } else {
                    cerr << "[ERROR] Multi-defined Transition." << endl;
                    exit(1);
                }
                if (!searchLoc((char*)loc_name_start.c_str(),
                                     &loc_start)) {
                    cerr << "[ERROR] Transition use undefined location" << endl;
                    exit(1);
                }
                if (regex_match(line, match, trans_pattern)) {
                    string loc_name_end = match[4];
                    if (!searchLoc((char*)loc_name_end.c_str(),
                                         &loc_end)) {
                        cerr << "[ERROR] Transition use undefined location"
                             << endl;
                        exit(1);
                    }
                    new_transition->set_locs(loc_start, loc_end);
                } else {
                    new_transition->set_locs(loc_start, loc_start);
                }
            } 
            else if (regex_match(line, match, invariant_pattern)) {
                if (new_poly && new_location) {
                    new_location->setPoly(new_poly);
                }
                if (new_poly && new_transition) {
                    new_transition->set_relation(new_poly);
                }
                if (new_poly && invariant_location) {
                    invariant_location->set_invariant_polyhedron(new_poly);
                }
                new_poly = NULL;
                new_location = NULL;
                invariant_location = NULL;
                new_transition = NULL;
                string locName = match[2];
                // cout<<locName<<" "<<locName.length()<<" "<<token<<endl;
                if (!searchLoc((char*)locName.c_str(),
                                     &invariant_location)) {
                    cerr << "[ERROR] undefined Invariant Location." << endl;
                    exit(1);
                }
            } else {
                if (!new_poly) {
                    if (stage == 1)
                        new_poly =
                            new C_Polyhedron(info->getDim(), UNIVERSE);
                    else
                        new_poly = new C_Polyhedron(2 * info->getDim(),
                                                    UNIVERSE);
                }
                sregex_iterator it(line.begin(), line.end(), term_pattern);
                sregex_iterator end;
                if (it == end) {
                    cerr << "[ERROR] No Matched Pattern, please check your "
                            "input."
                         << endl;
                    exit(1);
                }
                bool is_negative = false;
                bool is_rhs = false;
                Linear_Expression* le = new Linear_Expression();
                Linear_Expression* right = new Linear_Expression();
                int op = 0;
                // 0 -> =; 1 -> <=;
                while (it != end) {
                    string term = it->str();
                    if (regex_match(term, match, primed_coef_var_pattern)) {
                        int coef = stoi(match[1]);
                        if (is_negative)
                            coef = -coef;
                        string var = match[2];
                        int index = info->search(var.c_str());
                        if (index == VAR_NOT_FOUND) {
                            cout << "[ERROR] Undefined variable " << var
                                 << endl;
                            exit(1);
                        }
                        Linear_Expression* res = new Linear_Expression(
                            abs(coef) *
                            Variable(index + info->getDim()));
                        if (!is_rhs) {
                            if (coef > 0)
                                (*le) += (*res);
                            else
                                (*le) -= (*res);
                        } else {
                            if (coef > 0)
                                (*right) += (*res);
                            else
                                (*right) -= (*res);
                        }
                        delete (res);
                    } else if (regex_match(term, match, coef_var_pattern)) {
                        int coef = stoi(match[1]);
                        if (is_negative)
                            coef = -coef;
                        string var = match[2];
                        // cout<<match[1]<<" "<<coef<<" "<<line<<endl;
                        int index = info->search(var.c_str());
                        if (index == VAR_NOT_FOUND) {
                            cout << "[ERROR] Undefined variable " << var
                                 << endl;
                            exit(1);
                        }
                        Linear_Expression* res =
                            new Linear_Expression(abs(coef) * Variable(index));
                        if (!is_rhs) {
                            if (coef > 0)
                                (*le) += (*res);
                            else
                                (*le) -= (*res);
                        } else {
                            if (coef > 0)
                                (*right) += (*res);
                            else
                                (*right) -= (*res);
                        }
                        delete (res);
                    } else if (regex_match(term, match, coef_pattern)) {
                        int coef = stoi(match[1]);
                        // cout<<match[1]<<" "<<coef<<" "<<line<<endl;
                        if (is_negative)
                            coef = -coef;
                        Linear_Expression* res =
                            new Linear_Expression(abs(coef));
                        if (!is_rhs) {
                            if (coef > 0)
                                (*le) += (*res);
                            else
                                (*le) -= (*res);
                        } else {
                            if (coef > 0)
                                (*right) += (*res);
                            else
                                (*right) -= (*res);
                        }
                        delete (res);
                    } else if (regex_match(term, match, primed_pattern)) {
                        int coef = 1;
                        // cout<<line<<" "<<term<<endl;
                        if (is_negative)
                            coef = -coef;
                        string var = match[1];

                        int index = info->search(var.c_str());
                        if (index == VAR_NOT_FOUND) {
                            cout << "[ERROR] Undefined variable " << var
                                 << endl;
                            exit(1);
                        }
                        Linear_Expression* res = new Linear_Expression(
                            abs(coef) *
                            Variable(index + info->getDim()));
                        if (!is_rhs) {
                            if (coef > 0)
                                (*le) += (*res);
                            else
                                (*le) -= (*res);
                        } else {
                            if (coef > 0)
                                (*right) += (*res);
                            else
                                (*right) -= (*res);
                        }
                        delete (res);
                    } else if (regex_match(term, match, var_pattern)) {
                        int coef = 1;
                        // cout<<line<<" "<<term<<endl;
                        if (is_negative)
                            coef = -coef;
                        string var = match[1];

                        int index = info->search(var.c_str());
                        if (index == VAR_NOT_FOUND) {
                            cout << "[ERROR] Undefined variable " << var
                                 << endl;
                            exit(1);
                        }
                        Linear_Expression* res =
                            new Linear_Expression(abs(coef) * Variable(index));
                        if (!is_rhs) {
                            if (coef > 0)
                                (*le) += (*res);
                            else
                                (*le) -= (*res);
                        } else {
                            if (coef > 0)
                                (*right) += (*res);
                            else
                                (*right) -= (*res);
                        }
                        delete (res);
                    } else if (regex_match(term, match, sign_pattern)) {
                        if (match[1] == "-")
                            is_negative = true;
                        else
                            is_negative = false;
                    } else if (regex_match(term, match, equality_pattern)) {
                        if (match[1] == "<=")
                            op = 1;
                        else if (match[1] == ">=")
                            op = 2;
                        else
                            op = 0;
                        is_rhs = true;
                        is_negative = false;
                    } else if (regex_match(term, match, empty_pattern)) {
                        it++;
                        continue;
                    } else {
                        cerr << "[ERROR] No Matched Pattern, please check your "
                                "input."
                             << endl;
                        exit(1);
                    }
                    it++;
                }
                Constraint* new_constraint;
                if (op == 2) {
                    new_constraint = new Constraint((*le) >= (*right));
                } else if (op == 1) {
                    new_constraint = new Constraint((*le) <= (*right));
                } else {
                    new_constraint = new Constraint((*le) == (*right));
                }
                new_poly->add_constraint(*new_constraint);
                delete (le);
                delete (right);
                delete (new_constraint);
            }
            continue;
        }
    }
    dimension = info->getDim();
    exit(0);
}