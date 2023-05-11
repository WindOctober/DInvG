
#include <iostream>
#include <vector>
#include <string>
#include "DualInvariantMap.h"
#include "Elimination.h"
#include "InvariantMap.h"
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
int num_context;
bool zero;
bool one;
int prop_steps;
int weave_time;
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

#define ONECONTEXT 0
#define GENDROP 1
#define MANYCONTEXT 2
#define BULLSHIT 3
#define NEW_MANYCONTEXT 401
#define NEW_2_MANYCONTEXT 402
#define NEW_3_MANYCONTEXT 403
#define NEWDFS_SEQUENCES 405
#define NEWDFS_SEQ_PROPAGATION 404
#define DEBUG 406
#define DEBUG_2 407
#define DEBUG_3 408
#define NO_PRINT_TREE 409
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
#define ZERO_ONLY 5
#define ONE_ONLY 6
#define ZERO_ONE 7
#define NO_INSTANTIATION 8
#define YES_FALSEPATH 9
#define NO_FALSEPATH 10
#define YES_TRSAT 11
#define NO_TRSAT 12
#define YES_EXITPATH 13
#define NO_EXITPATH 14
#define YES_DJINV 17
#define NO_DJINV 18
#define YES_ARRINV 19
#define NO_ARRINV 20
#define NO_DUAL 21
#define INV_CHECK 15
#define NO_INV_CHECK 16

vector<int>** location_matrix;
int location_count = 0;
int global_binary_i = 0;
long int global_contains_time = 0;
vector<int> target_prior;

vector<string> Vars;
int max_prop_steps;
vector<Location*> Locations;
vector<TransitionRelation*> Transitions;

char err_str[100];
int dimension;
var_info *f, *fd, *fm;
vector<Location*>* loclist;
vector<TransitionRelation*>* trlist;
Context* glc;  // The global context
vector<Context*>* children;
vector<System*>* global_sub_system_list;
System* global_system;
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
C_Polyhedron* invd;
Counter counter;
bool inv_check;

void collect_generators(vector<Context*>* children, Generator_System& g);
int parse_cmd_line(char* x);
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

int* tt;
int debug, debug_2, debug_3;
bool print_tree;
bool falsepath;
bool trsat;
bool noexitpath;
bool djinv;
bool arrinv;
bool search_location(char* w, Location** m);
bool search_transition_relation(char* w, TransitionRelation** m);
int find_variable(char* what);
void add_preloc_invariants_to_transitions();
void print_status();
void print_bake_off(InvariantMap const& what);

void check_invariant_ok();

void do_some_propagation() {
    // try and fire each transition relation

    vector<TransitionRelation*>::iterator vi;
    int fired_up = 0;
    int ntrans = trlist->size();

    while (fired_up < prop_steps * ntrans) {
        for (vi = trlist->begin(); vi < trlist->end(); vi++) {
            (*vi)->fire();
            fired_up++;
        }
    }
}

Location * get_location(char* name) {
    vector<Location*>::iterator vi;
    string nstr(name);
    for (vi = loclist->begin(); vi < loclist->end(); vi++) {
        if ((*vi)->matches(nstr)) {
            return *vi;
        }
    }
    fprintf(stderr, "Error: location %s not found\n", name);
    exit(1);
}

bool search_location( char * name, Location ** what){
   vector<Location*>::iterator vi;
   string nstr(name);
   for(vi=loclist->begin();vi< loclist->end();vi++){
      if ((*vi)->matches(nstr)){
         *what=(*vi);
         return true;
      }
   }

   return false;
}

bool search_transition_relation( char * name, TransitionRelation ** what){
   vector<TransitionRelation*>::iterator vi;
   string nstr(name);
   for(vi=trlist->begin();vi< trlist->end();vi++){
      if ((*vi)->matches(nstr)){
         *what=(*vi);
         return true;
      }
   }
   
   return false;
}

int parse_cmd_line(char* x) {
    if (strcmp(x, "debug") == 0)
        return DEBUG;
    if (strcmp(x, "debug_2") == 0)
        return DEBUG_2;
    if (strcmp(x, "debug_3") == 0)
        return DEBUG_3;
    if (strcmp(x, "no_print_tree") == 0)
        return NO_PRINT_TREE;
    if (strcmp(x, "newdfs_sequences") == 0)
        return NEWDFS_SEQUENCES;
    if (strcmp(x, "newdfs_seq_propagation") == 0)
        return NEWDFS_SEQ_PROPAGATION;
    if (strcmp(x, "noProjection") == 0)
        return NO_PROJECTION;
    if (strcmp(x, "FEC") == 0)
        return FARKAS_ELIMINATE_C;
    if (strcmp(x, "KEC") == 0)
        return KOHLER_ELIMINATE_C;
    if (strcmp(x, "REC") == 0)
        return FOUMOT_ELIMINATE_C;
    if (strcmp(x, "no_prior") == 0)
        return NO_PRIOR;
    if (strcmp(x, "target_prior1") == 0)
        return TARGET_PRIOR1;
    if (strcmp(x, "target_prior2") == 0)
        return TARGET_PRIOR2;
    if (strcmp(x, "target_prior3") == 0)
        return TARGET_PRIOR3;
    if (strcmp(x, "one_per_group") == 0)
        return ONE_PER_GROUP;
    if (strcmp(x, "two_per_group") == 0)
        return TWO_PER_GROUP;
    if (strcmp(x, "three_per_group") == 0)
        return THREE_PER_GROUP;
    if (strcmp(x, "four_per_group") == 0)
        return FOUR_PER_GROUP;
    if (strcmp(x, "gendrop") == 0)
        return GENDROP;
    if (strcmp(x, "zero_only") == 0)
        return ZERO_ONLY;
    if (strcmp(x, "one_only") == 0)
        return ONE_ONLY;
    if (strcmp(x, "zero_one") == 0)
        return ZERO_ONE;
    if (strcmp(x, "falsepath") == 0)
        return YES_FALSEPATH;
    if (strcmp(x, "nofalsepath") == 0)
        return NO_FALSEPATH;
    if (strcmp(x, "trsat") == 0)
        return YES_TRSAT;
    if (strcmp(x, "notrsat") == 0)
        return NO_TRSAT;
    if (strcmp(x, "exitpath") == 0)
        return YES_EXITPATH;
    if (strcmp(x, "noexitpath") == 0)
        return NO_EXITPATH;
    if (strcmp(x, "djinv") == 0)
        return YES_DJINV;
    if (strcmp(x, "nodjinv") == 0)
        return NO_DJINV;
    if (strcmp(x, "arrinv") == 0)
        return YES_ARRINV;
    if (strcmp(x, "noarrinv") == 0)
        return NO_ARRINV;
    if (strcmp(x, "nodual") == 0)
        return NO_DUAL;
    if (strcmp(x, "invcheck") == 0)
        return INV_CHECK;
    if (strcmp(x, "noinvcheck") == 0)
        return NO_INV_CHECK;

    return BULLSHIT;
}
void Print_Location();

void collect_invariants(C_Polyhedron& cpoly, C_Polyhedron& invd) {
    /*
     *  Collect invariants
     */
    vector<Location*>::iterator vl;
    invd = C_Polyhedron(fd->get_dimension(), UNIVERSE);
    vl = loclist->begin();
    // cout<<endl<<"- In collect_invariants(), cpoly is : "<<endl<<"
    // "<<cpoly<<endl; Generator_System mgs = cpoly.minimized_generators();
    for (vl = loclist->begin(); vl < loclist->end(); vl++) {
        (*vl)->extract_invariants_and_update(cpoly, invd);
        //(*vl)->extract_invariant_from_generator(mgs);
        //(*vl)->update_dual_constraints(invd);
        // cout<<endl<<"5.";
        // Print_Location();
    }
    return;
}

void collect_invariants_for_one_location_by_eliminating(int target_index,
                                                        C_Polyhedron& cpoly,
                                                        C_Polyhedron& invd) {
    //
    //  Collect invariants for initial
    //
    invd = C_Polyhedron(fd->get_dimension(), UNIVERSE);
    //    Firstly, collect invariants for initial location by eliminating
    //      for initial *vl, i.e. location,
    //      use cpoly to update *vl->invariant and *vl->invariant updates invd.
    (*loclist)[target_index]
        ->extract_invariants_and_update_for_one_location_by_eliminating(cpoly,
                                                                        invd);

    return;
}


void dfs_sequences_generation_traverse(
    vector<vector<vector<vector<int>>>>& target_sequences,
    int target_index,
    vector<Clump>& vcl,
    C_Polyhedron& initp) {
    // C_Polyhedron invd(*trivial);
    Tree tr = Tree();  // empty tree
    tr.set_target_index(target_index);
    // int ncl=0;
    vector<Clump>::iterator vi;
    for (vi = vcl.begin(); vi < vcl.end(); vi++) {
        // ncl++;
        (*vi).clear();
    }

    cout << endl
         << endl
         << "/ Start to solve Location "
         << (*loclist)[target_index]->get_name();
    if (tree_prior == "no_prior") {
        cout << endl << "/ Using no_prior";
        tr.Original_Prior(vcl);
    } else if (tree_prior == "target_prior1") {
        cout << endl << "/ Using target_prior1";
        tr.Reorder_Target_Prior_1(vcl);
    } else if (tree_prior == "target_prior2") {
        cout << endl << "/ Using target_prior2";
        tr.Reorder_Target_Prior_2(vcl);
    } else if (tree_prior == "target_prior3") {
        cout << endl << "/ Using target_prior3";
        tr.Reorder_Target_Prior_3(vcl);
    } else {
        cout << endl << "Wrong Type: " << tree_prior;
    }

    tr.set_max_clump_count();
    // tr.prune_clumps_by_hierarchy_inclusion();
    // dfs_traverse_recursive_for_one_location_by_eliminating(target_index,ncl,tr,initp,invd);

    cout << endl << "/ Generate Sequences";
    vector<vector<vector<int>>> sequences;
    sequences = tr.sequences_generation(some_per_group, initp);
    target_sequences.push_back(sequences);
}

void dfs_sequences_generation_traverse_for_one_location_from_intra(
    vector<vector<vector<vector<int>>>>& target_sequences,
    int target_index,
    vector<Clump>& vcl,
    C_Polyhedron& initp) {
    // C_Polyhedron invd(*trivial);
    Tree tr = Tree();  // empty tree
    tr.set_target_index(target_index);
    vector<Clump>::iterator vi;
    for (vi = vcl.begin(); vi < vcl.end(); vi++) {
        (*vi).clear();
    }

    cout << endl
         << endl
         << "/ Start to solve Location "
         << (*loclist)[target_index]->get_name();
    // extract only-one-vcl which is intra-transition about this location
    tr.extract_vcl_for_one_location_about_intra(vcl);

    tr.set_max_clump_count();

    cout << endl << "/ Generate Sequences";
    vector<vector<vector<int>>> sequences;
    sequences = tr.sequences_generation("one_per_group", initp);
    target_sequences.push_back(sequences);

    cout << endl << "\\ Generate Sequences";
    cout << endl
         << "\\ End to solve Location " << (*loclist)[target_index]->get_name();
}

void dfs_sequences_traverse_for_one_location_by_eliminating(
    vector<vector<vector<int>>> sequences,
    int target_index,
    vector<Clump>& vcl,
    C_Polyhedron& initp) {
    C_Polyhedron invd(*trivial);
    Tree tr = Tree();  // empty tree
    tr.set_target_index(target_index);
    // int ncl=0;
    vector<Clump>::iterator vi;
    for (vi = vcl.begin(); vi < vcl.end(); vi++) {
        // ncl++;
        (*vi).clear();
    }

    cout << endl
         << endl
         << "/ Start to solve Location "
         << (*loclist)[target_index]->get_name();
    if (tree_prior == "no_prior") {
        cout << endl << "/ Using no_prior";
        tr.Original_Prior(vcl);
    } else if (tree_prior == "target_prior1") {
        cout << endl << "/ Using target_prior1";
        tr.Reorder_Target_Prior_1(vcl);
    } else if (tree_prior == "target_prior2") {
        cout << endl << "/ Using target_prior2";
        tr.Reorder_Target_Prior_2(vcl);
    } else if (tree_prior == "target_prior3") {
        cout << endl << "/ Using target_prior3";
        tr.Reorder_Target_Prior_3(vcl);
    } else {
        cout << endl << "Wrong Type: " << tree_prior;
    }

    tr.set_max_clump_count();
    // tr.prune_clumps_by_hierarchy_inclusion();
    // dfs_traverse_recursive_for_one_location_by_eliminating(target_index,ncl,tr,initp,invd);

    // cout<<endl;
    cout << endl << "/ Read(Traverse) Sequences";
    tr.dfs_sequences_traverse(sequences, initp, invd);
}

void dfs_sequences_traverse_for_one_location_from_intra_by_eliminating(
    vector<vector<vector<int>>> sequences,
    int target_index,
    vector<Clump>& vcl,
    C_Polyhedron& initp) {
    C_Polyhedron invd(*trivial);
    Tree tr = Tree();  // empty tree
    tr.set_target_index(target_index);
    vector<Clump>::iterator vi;
    for (vi = vcl.begin(); vi < vcl.end(); vi++) {
        (*vi).clear();
    }

    cout << endl
         << endl
         << "/ Start to solve Location "
         << (*loclist)[target_index]->get_name();
    // extract only-one-vcl which is intra-transition about this location
    tr.extract_vcl_for_one_location_about_intra(vcl);

    tr.set_max_clump_count();

    cout << endl << "/ Read(Traverse) Sequences";
    tr.dfs_sequences_traverse(sequences, initp, invd);

    cout << endl << "\\ Read(Traverse) Sequences";
    cout << endl
         << "\\ End to solve Location " << (*loclist)[target_index]->get_name();
}

// compute invariants by farkas for this one location from intra-transition
void collect_invariants_for_one_location_from_intra(vector<Clump>& vcl,
                                                    int loc_index) {
    // initialize
    int lid = loc_index;
    vector<vector<vector<vector<int>>>> target_sequences;
    int nd = fd->get_dimension();
    C_Polyhedron local_initp(nd, UNIVERSE);

    /*
     * Generate Sequences
     */
    if (debug_3) {
        cout << endl;
        cout << endl
             << "- id (Generate Sequences): " << lid
             << ", Location::" << (*loclist)[lid]->get_name();
    }
    single_pre_prune_bang_count = 0;
    counter.set_location_index_and_init_depth(lid, vcl.size());
    // compute invariants by using initial-value and intra-transition
    bool has_initial_polyset = (*loclist)[lid]->has_initial();
    if (!has_initial_polyset) {
        cout << endl
             << "- ( !has_initial_polyset ) in Location::"
             << (*loclist)[lid]->get_name();
        vector<vector<vector<int>>> empty_sequences;
        target_sequences.push_back(empty_sequences);
    } else {
        (*loclist)[lid]->compute_dual_constraints(local_initp);
        dfs_sequences_generation_traverse_for_one_location_from_intra(
            target_sequences, lid, vcl, local_initp);
    }

    /*
     * Read Sequences
     */
    if (debug_3) {
        cout << endl;
        cout << endl
             << "- id (Read Sequences): " << lid
             << ", Location::" << (*loclist)[lid]->get_name();
    }
    single_weave_count = 0;
    single_collect_time = 0;
    single_post_prune_bang_count = 0;
    // compute invariants by using initial-value and intra-transition
    if (!has_initial_polyset) {
        cout << endl
             << "- ( !has_initial_polyset ) in Location::"
             << (*loclist)[lid]->get_name();
    } else {
        vector<vector<vector<int>>> sequences;
        if (target_sequences.size() == 1) {
            sequences = target_sequences[0];
        } else {
            cout << endl << "Error: There are more than one sequences";
        }
        dfs_sequences_traverse_for_one_location_from_intra_by_eliminating(
            sequences, lid, vcl, local_initp);
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
    fm = new var_info();
    fd = new var_info();
    loclist = new vector<Location*>();
    trlist = new vector<TransitionRelation*>();
    debug = 0;
    debug_2 = 0;
    debug_3 = 0;
    print_tree = true;
    num_context = 1;
    projection = "kohler_improvement_eliminate_c";
    tree_prior = "target_prior2";
    some_per_group = "two_per_group";
    gendrop = false;
    global_sub_system_list = new vector<System*>();
    zero = one = true;
    falsepath = true;
    trsat = true;
    noexitpath = false;
    djinv = false;
    arrinv = false;
    prop_steps = 2;
    weave_time = 360000;
    total_time = 360000;
    cout << "Done!" << endl;
}

void Print_Location_and_Transition() {
    cout << endl;
    cout << "----------------------------- " << endl;
    cout << "| The Locations read in are: " << endl;
    cout << "----------------------------- " << endl;
    for (vector<Location*>::iterator vi = loclist->begin(); vi < loclist->end();
         vi++) {
        cout << *(*vi);
    }
    cout << "----------------------------- " << endl;
    cout << "| The Transitions read in are: " << endl;
    cout << "----------------------------- " << endl;
    for (vector<TransitionRelation*>::iterator vj = trlist->begin();
         vj < trlist->end(); vj++) {
        cout << *(*vj);
    }
}

void Print_Location() {
    cout << endl;
    cout << "----------------------------- " << endl;
    cout << "| The Locations read in are: " << endl;
    cout << "----------------------------- " << endl;
    for (vector<Location*>::iterator vi = loclist->begin(); vi < loclist->end();
         vi++) {
        cout << *(*vi);
    }
}

void print_disjunctive_inv_before_program() {
    cout << endl << "/---------------------------------------- ";
    cout << endl << "| Disjunctive Invariants before Program: ";
    cout << endl << "----------------------------------------- ";
    int i = 0;
    for (vector<Location*>::iterator vi = loclist->begin(); vi < loclist->end();
         vi++) {
        if ((*vi)->get_name() != EXIT_LOCATION &&
            !(*vi)->get_invariant().is_empty()) {
            if (i != 0) {
                cout << endl << "\\/";
            }
            print_pure_polyhedron((*vi)->get_invariant(),
                                  (*vi)->get_var_info());
            i++;
        }
    }
    cout << endl << "\\---------------------------------------- ";
    cout << endl;
}

void print_array_inv_before_program() {
    cout << endl << "/---------------------------------------- ";
    cout << endl << "| Array Invariants before Program: ";
    cout << endl << "----------------------------------------- ";
    int i = 0;
    for (vector<Location*>::iterator vi = loclist->begin(); vi < loclist->end();
         vi++) {
        if ((*vi)->get_name() != EXIT_LOCATION &&
            !(*vi)->get_invariant().is_empty()) {
            if (i != 0) {
                cout << endl << "\\/";
            }
            print_pure_polyhedron_for_arrayinv((*vi)->get_invariant(),
                                               (*vi)->get_var_info());
            i++;
        }
    }
    cout << endl << "\\---------------------------------------- ";
    cout << endl;
}

void Print_Status_before_Solver() {
    cout << endl;
    cout << "/----------------------------- " << endl;
    cout << "| Status before Solver: " << endl;
    cout << "----------------------------- " << endl;
    cout << "| Debug ID # " << debug << endl;
    cout << "| Debug_2 ID # " << debug_2 << endl;
    cout << "| Debug_3 ID # " << debug_3 << endl;
    cout << "| Print Tree : " << print_tree << endl;
    cout << "| Strategy ID # " << num_context << endl;
    cout << "| Strategy name : ";
    switch (num_context) {
        case 1:
            cout << "newdfs_sequences" << endl;
            break;
        case 2:
            cout << "newdfs_seq_propagation" << endl;
            break;
        default:
            cout << "Undefined Strategy" << endl;
            break;
    }

    cout << "| DFS Search method : " << tree_prior << endl;
    cout << "| Sequences Divide method : " << some_per_group << endl;
    cout << "| Projection method : " << projection << endl;
    cout << "| Local invariants to be generated : " << zero << endl;
    cout << "| Increasing invariants to be generated : " << one << endl;
    cout << "| Falsepath to be enabled : " << falsepath << endl;
    cout << "| Transition-sat to be enabled : " << trsat << endl;
    cout << "| Exit-Transition is computed : " << (!noexitpath) << endl;
    cout << "| Display Disjunctive Invariants : " << djinv << endl;
    cout << "| Display Array Invariants : " << arrinv << endl;
    cout << "| Weave time allowed : " << weave_time << endl;
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

    cout << "| # of pruned vcl in intra-transition = " << prune_count << endl;
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
    if (num_context != 1) {
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
    }
    cout << "|" << endl;

    cout << "| TOTAL Time = " << total_timer.compute_time_elapsed() << endl;
    cout << "\\----------------------------- " << endl;
}

int get_index_of_location(string loc_name) {
    int i = 0;
    for (vector<Location*>::iterator vi = loclist->begin(); vi < loclist->end();
         vi++) {
        if ((*vi)->get_name() == loc_name) {
            return i;
        }
        i++;
    }
}

int get_index_of_transition(string name) {
    int i = 0;
    for (vector<TransitionRelation*>::iterator vi = trlist->begin();
         vi < trlist->end(); vi++) {
        if ((*vi)->get_name() == name) {
            return i;
        }
        i++;
    }
}

// return the transition-index which is start from this pre-location-index
vector<int> get_tid_from_prelid(int prelid) {
    vector<int> tid;
    int trlist_size = trlist->size();

    for (int ti = 0; ti < trlist_size; ti++) {
        if ((*trlist)[ti]->get_preloc_index() == prelid) {
            tid.push_back(ti);
        }
    }

    return tid;
}

// return the transition-index which is start from this pre-location-index
// except intra-transition
vector<int> get_intertid_from_prelid(int prelid) {
    vector<int> tid;
    int trlist_size = trlist->size();

    for (int ti = 0; ti < trlist_size; ti++) {
        if ((*trlist)[ti]->get_preloc_index() == prelid &&
            (*trlist)[ti]->get_postloc_index() != prelid) {
            tid.push_back(ti);
        }
    }

    return tid;
}


// return the transition-index
// which is start from this pre-location-index except intra-transition
// and except someother transition-index
vector<int> get_intertid_from_prelid_without_some(int prelid, string some) {
    vector<int> tid;
    int trlist_size = trlist->size();

    for (int ti = 0; ti < trlist_size; ti++) {
        if ((*trlist)[ti]->get_preloc_index() == prelid &&
            (*trlist)[ti]->get_postloc_index() != prelid &&
            (*trlist)[ti]->get_postloc_name() != some) {
            tid.push_back(ti);
        }
    }

    return tid;
}

// return the inter-transition-index which is end at this post-location-index
vector<int> get_intertid_to_postlid(int postlid) {
    vector<int> tid;
    int trlist_size = trlist->size();

    for (int ti = 0; ti < trlist_size; ti++) {
        if ((*trlist)[ti]->get_postloc_index() == postlid &&
            (*trlist)[ti]->get_preloc_index() != postlid) {
            tid.push_back(ti);
        }
    }

    return tid;
}

void Create_Adjacency_Matrix_for_Location_and_Transition() {
    //  matrix initialization
    //    count the number of locations, i.e. length of matrix
    int loclist_size = loclist->size();
    //    count the number of transitions and push back to the vector
    // vector<int> location_matrix[loclist_size][loclist_size];
    location_matrix = new vector<int>*[loclist_size];
    for (int i = 0; i < loclist_size; i++) {
        location_matrix[i] = new vector<int>[loclist_size];
    }

    int j = 0, j1 = 0;
    for (vector<TransitionRelation*>::iterator vj = trlist->begin();
         vj < trlist->end(); vj++) {
        if (trsat) {
            if (!(*vj)->get_relation().is_empty()) {
                location_matrix[get_index_of_location((*vj)->get_preloc_name())]
                               [get_index_of_location(
                                    (*vj)->get_postloc_name())]
                                   .push_back(j);
                j1++;
            }
            j++;
        } else {
            location_matrix[get_index_of_location((*vj)->get_preloc_name())]
                           [get_index_of_location((*vj)->get_postloc_name())]
                               .push_back(j);
            j1++;
            j++;
        }
    }

    //  print the matrix
    cout << endl << "/----------------------------- ";
    cout << endl << "| Adjacency Matrix for Location and Transition: ";
    cout << endl << "---------------------------- ";
    cout << endl << "| Input: " << trlist->size() << " transitions";
    cout << endl << "----------------------------- ";
    cout << endl << "| [#] is transition_index";
    for (int i = 0; i < loclist_size; i++) {
        cout << endl << "| " << (*loclist)[i]->get_name() << ": ";
        for (int j = 0; j < loclist_size; j++) {
            cout << "[";
            for (vector<int>::iterator it = location_matrix[i][j].begin();
                 it < location_matrix[i][j].end(); it++) {
                cout << " " << *it << " ";
            }
            cout << "]->" << (*loclist)[j]->get_name() << ";  ";
        }
    }
    cout << endl << "----------------------------- ";
    cout << endl << "| Output: " << j1 << " transitions";
    cout << endl << "\\----------------------------- ";
}

void Clear_Location_Invariant() {
    for (vector<Location*>::iterator vl = loclist->begin(); vl < loclist->end();
         vl++) {
        cout << endl
             << "- Location " << (*vl)->get_name() << ": initialize invariant";
        (*vl)->initialize_invariant();
    }
}

void Initial_with_input() {
    f = new var_info();
    for (int i = 0; i < Vars.size(); i++) {
        f->search_and_insert(Vars[i].c_str());
    }
    dimension = f->get_dimension();

    prop_steps = max_prop_steps;
    // Requires: Locations have set initial assertions, possible invariant
    // assertions.
    for (int i = 0; i < Locations.size(); i++) {
        loclist->push_back(Locations[i]);
    }
    // Requires: Transitions have set locs, trans relations.
    for (int i = 0; i < Transitions.size(); i++) {
        trlist->push_back(Transitions[i]);
    }
    return;
}

void Scan_Input_2(int argc, char *argv[]) {
    cout << endl << "- Parsing Input Doing...";
    
    char line[100];
    char *token, *token1, *token2;
    f = new var_info();
    Location *loc;
    TransitionRelation *tr;

    // read each line
    while (fgets(line, sizeof(line), stdin)) {

        // input variable
        if (strstr(line, "variable [ ") != NULL) {
            // extract variables
            token = strtok(line, " ");
            while (token != NULL) {
                token = strtok(NULL, " ");
                if (token != NULL && token[0] != '[' && token[0] != ']') {
                    f->search_and_insert(token);
                }
            }
            dimension = f->get_dimension();
        }

        // input Location
        if (strstr(line, "Location ") != NULL) {
            token = strtok(line, " \n");
            while (token != NULL) {
                token = strtok(NULL, " \n");
                if (token != NULL) {
                    // search loclist for the identifier
                    Location *what;
                    if (!search_location(token, &what)){
                        loc = new Location(dimension,f,fd,fm,token);
                        loclist->push_back(loc);
                    }
                    else {
                        cout << endl<< "Error: Location " << token << " already exists.";
                        loc = what; // set loc to the existing location, but it is not added to loclist
                    }
                }
            }
        }

        // input transition
        // if (strstr(line, "transition ") != NULL) {
        //     token = strtok(line, " :,\n");
        //     token = strtok(NULL, " :,\n");
        //     TransitionRelation *what;
        //     if (!search_transition_relation(token, &what)){
        //         tr = new TransitionRelation(dimension,f,fd,fm,token);
        //         trlist->push_back(tr);
        //     }
        //     else {
        //         cout << endl<< "Error: Transition " << token << " already exists.";
        //         tr = what; // set tr to the existing transition, but it is not added to trlist
        //     }
        //     // token = strtok(NULL, " :,\n");
        //     // token1 = token;
        //     // token = strtok(NULL, " :,\n");
        //     // token2 = token;
        //     // tr->set_locs(get_location(token1), get_location(token2));
        // }
    }

    cout << endl << "- Parsing Input Done...";
}

void Scan_Input() {
    cout << endl << "- Parsing Input Doing...";

    cout << endl
         << "please input all the variable you want to use and end with 0:";
    while (true) {
        string name;
        cin >> name;
        if (name == "0")
            break;
        Vars.push_back(name);
    }
    cout << endl << "Finish parsing vars.";
    cout << endl
         << "please input all the Location you want to use and end with 0:";
    while (true) {
        int flag;
        Location* loc;
        string name;
        cout<<endl<<"Does this is the initial Location with initial assertion? if input 1 then yes else input 2 then no else exit";
        cin>>flag;
        if (flag==1){
            cin>>name;
            cout<<endl<<"Location name is "<<name;
            
        }
        else if (flag==2){
            
        }
        else break;
    }
    cout << "Done!" << endl;
}

int main(int argc, char* argv[]) {
    ios::sync_with_stdio(false);
    total_timer.restart();
    Initialize_before_Parser();
    //Scan_Input();
    Scan_Input_2(argc, argv);
    Initial_with_input();
    add_preloc_invariants_to_transitions();
    Print_Status_before_Solver();
    Print_Location_and_Transition();
    Create_Adjacency_Matrix_for_Location_and_Transition();

    global_system = new System(f, fd, fm);
    for (vector<Location*>::iterator vi = loclist->begin(); vi < loclist->end();
         vi++) {
        global_system->add_location((*vi));
    }
    for (vector<TransitionRelation*>::iterator vj = trlist->begin();
         vj < trlist->end(); vj++) {
        global_system->add_transition((*vj));
    }
    global_system->compute_duals();

    if (num_context == 1) {
        //  output_file: **newdfs_sequences**

        //  nd
        int nd = fd->get_dimension();
        //  trivial
        trivial = new C_Polyhedron(nd, UNIVERSE);
        for (vector<Location*>::iterator vi = loclist->begin();
             vi < loclist->end(); vi++) {
            (*vi)->add_to_trivial(trivial);
        }
        //  initp
        C_Polyhedron initp(nd, UNIVERSE);
        for (vector<Location*>::iterator vi = loclist->begin();
             vi < loclist->end(); vi++) {
            (*vi)->make_context();
            (*vi)->compute_dual_constraints(initp);
        }
        //  vcl
        vector<Clump> vcl;
        for (vector<TransitionRelation*>::iterator vj = trlist->begin();
             vj < trlist->end(); vj++) {
            (*vj)->compute_consecution_constraints(vcl, initp);
            if (total_timer.compute_time_elapsed() >= weave_time) {
                cout << "Time is up!" << endl;
                break;
            }
        }
        for (vector<Location*>::iterator vi = loclist->begin();
             vi < loclist->end(); vi++) {
            (*vi)->add_clump(vcl);
            if (total_timer.compute_time_elapsed() >= weave_time) {
                cout << "Time is up!" << endl;
                break;
            }
            //    this also should trigger the simplification of the context
        }

        /*
         * The main body of CNF-to-DNF Conversion
         *   dfs_sequences_generation_traverse
         *   dfs_sequences_traverse_for_one_location_by_eliminating
         */
        dfs_traverse_timer.restart();
        vector<vector<vector<vector<int>>>> target_sequences;
        for (int target_index = 0; target_index < loclist->size();
             target_index++) {
            if (total_timer.compute_time_elapsed() >= total_time) {
                cout << endl << "Time is up!";
                break;
            }

            single_pre_prune_bang_count = 0;
            counter.set_location_index_and_init_depth(target_index, vcl.size());
            single_dfs_sequences_generation_timer.restart();

            dfs_sequences_generation_traverse(target_sequences, target_index,
                                              vcl, initp);

            single_dfs_sequences_generation_timer.stop();
            vector_single_dfs_sequences_generation_time.push_back(
                single_dfs_sequences_generation_timer.compute_time_elapsed());
            vector_single_pre_prune_bang_count.push_back(
                single_pre_prune_bang_count);
        }
        // Clear_Location_Invariant();
        for (int target_index = 0; target_index < loclist->size();
             target_index++) {
            if (total_timer.compute_time_elapsed() >= total_time) {
                cout << endl << "Time is up!";
                break;
            }

            single_weave_count = 0;
            single_collect_time = 0;    
            single_post_prune_bang_count = 0;
            single_dfs_sequences_traverse_timer.restart();

            vector<vector<vector<int>>> sequences =
                target_sequences[target_index];
            dfs_sequences_traverse_for_one_location_by_eliminating(
                sequences, target_index, vcl, initp);

            single_dfs_sequences_traverse_timer.stop();
            vector_single_dfs_sequences_traverse_time.push_back(
                single_dfs_sequences_traverse_timer.compute_time_elapsed());
            vector_single_weave_count.push_back(single_weave_count);
            vector_single_collect_time.push_back(single_collect_time);
            vector_single_post_prune_bang_count.push_back(
                single_post_prune_bang_count);
        }
        dfs_traverse_timer.stop();
        dfs_traverse_time = dfs_traverse_timer.compute_time_elapsed();
    } else if (num_context == 2) {
        //  output_file: **newdfs_seq_propagation**
        //  nd
        int nd = fd->get_dimension();
        //  trivial
        trivial = new C_Polyhedron(nd, UNIVERSE);
        for (vector<Location*>::iterator vi = loclist->begin();
             vi < loclist->end(); vi++) {
            (*vi)->add_to_trivial(trivial);
        }
        //  initp
        C_Polyhedron initp(nd, UNIVERSE);
        for (vector<Location*>::iterator vi = loclist->begin();
             vi < loclist->end(); vi++) {
            (*vi)->make_context();
            (*vi)->compute_dual_constraints(initp);
        }
        //  vcl
        vector<Clump> vcl;
        for (vector<TransitionRelation*>::iterator vj = trlist->begin();
             vj < trlist->end(); vj++) {
            (*vj)->compute_consecution_constraints(vcl, initp);
            if (total_timer.compute_time_elapsed() >= weave_time) {
                cout << "Time is up!" << endl;
                break;
            }
        }
        for (vector<Location*>::iterator vi = loclist->begin();
             vi < loclist->end(); vi++) {
            (*vi)->add_clump(vcl);
            if (total_timer.compute_time_elapsed() >= weave_time) {
                cout << "Time is up!" << endl;
                break;
            }
            //    this also should trigger the simplification of the context
        }

        /*
         * The main body of CNF-to-DNF Conversion
         *   dfs_sequences_generation_traverse
         *   dfs_sequences_traverse_for_one_location_by_eliminating
         */
        // Generate Sequences
        dfs_traverse_timer.restart();
        vector<vector<vector<vector<int>>>> target_sequences;
        for (int target_index = 0; target_index < loclist->size();
             target_index++) {
            if (debug_3) {
                cout << endl
                     << "- target_index (Generate Sequences): " << target_index
                     << ", Location::" << (*loclist)[target_index]->get_name();
            }
            single_pre_prune_bang_count = 0;
            counter.set_location_index_and_init_depth(target_index, vcl.size());
            single_dfs_sequences_generation_timer.restart();

            // only compute invariants at initial location
            bool has_initial_poly_set =
                (*loclist)[target_index]->initial_poly_set();
            if (!has_initial_poly_set) {
                cout << endl
                     << "- ( !has_initial_poly_set ) in Location::"
                     << (*loclist)[target_index]->get_name();
                vector<vector<vector<int>>> empty_sequences;
                target_sequences.push_back(empty_sequences);
            } else {
                dfs_sequences_generation_traverse(target_sequences,
                                                  target_index, vcl, initp);
            }

            single_dfs_sequences_generation_timer.stop();
            vector_single_dfs_sequences_generation_time.push_back(
                single_dfs_sequences_generation_timer.compute_time_elapsed());
            vector_single_pre_prune_bang_count.push_back(
                single_pre_prune_bang_count);
        }
        // Read Sequences
        for (int target_index = 0; target_index < loclist->size();
             target_index++) {
            if (debug_3) {
                cout << endl
                     << "- target_index (Read Sequences): " << target_index
                     << ", Location::" << (*loclist)[target_index]->get_name();
            }
            single_weave_count = 0;
            single_collect_time = 0;
            single_post_prune_bang_count = 0;
            single_dfs_sequences_traverse_timer.restart();

            // only compute invariants at initial location
            bool has_initial_poly_set =
                (*loclist)[target_index]->initial_poly_set();
            if (!has_initial_poly_set) {
                cout << endl
                     << "- ( !has_initial_poly_set ) in Location::"
                     << (*loclist)[target_index]->get_name();
            } else {
                vector<vector<vector<int>>> sequences =
                    target_sequences[target_index];
                dfs_sequences_traverse_for_one_location_by_eliminating(
                    sequences, target_index, vcl, initp);
            }

            single_dfs_sequences_traverse_timer.stop();
            vector_single_dfs_sequences_traverse_time.push_back(
                single_dfs_sequences_traverse_timer.compute_time_elapsed());
            vector_single_weave_count.push_back(single_weave_count);
            vector_single_collect_time.push_back(single_collect_time);
            vector_single_post_prune_bang_count.push_back(
                single_post_prune_bang_count);
        }
        dfs_traverse_timer.stop();
        dfs_traverse_time = dfs_traverse_timer.compute_time_elapsed();

        /*
         * The main body of Propagation
         */

        // Test1: propagate invariants from initial location to all others
        // propagate_invariants_from_initial_location_to_all_others();

        // compute other invariants by propagation with Farkas
        // ::First, compute other location except Initial & Exit-Location
        // ::Second, compute Exit-Location
        compute_invariants_by_propagation_with_farkas(vcl);
    }
    total_timer.stop();
    Print_Location();
    if (djinv) {
        print_disjunctive_inv_before_program();
    }
    if (arrinv) {
        print_array_inv_before_program();
    }
    Print_Status_after_Solver();

#ifndef TRACE
    // only print exit-location
    for (vector<Location*>::iterator vi = loclist->begin(); vi < loclist->end();
         vi++) {
        if ((*vi)->get_name() == EXIT_LOCATION) {
            if ((*vi)->get_vp_inv_flag()) {
                cout << "Location: " << (*vi)->get_name();
                cout << endl;
                nt_print_pure_clump((*vi)->get_vp_inv(), (*vi)->get_var_info());
            } else {
                cout << "Location: " << (*vi)->get_name();
                nt_print_pure_polyhedron((*vi)->get_invariant(),
                                         (*vi)->get_var_info());
            }
        }
    }
#endif
    if (inv_check) {
        check_invariant_ok();
    }
    return 0;
}

void collect_generators(vector<Context*>* children, Generator_System& g) {
    vector<Context*>::iterator vk;
    for (vk = children->begin(); vk < children->end(); vk++) {
        (*vk)->collect_generators(g);
    }
}

void add_preloc_invariants_to_transitions() {
    vector<TransitionRelation*>::iterator vtr;
    for (vtr = trlist->begin(); vtr < trlist->end(); ++vtr) {
        (*vtr)->add_preloc_invariant();
    }
    return;
}

void print_status() {
    cout << "---------------------------------------------------" << endl;
    cout << " Local invariants to be generated : " << zero << endl;
    cout << " Increasing invariants to be generated : " << one << endl;
    cout << " Strategy ID #" << num_context << endl;
    cout << " # of initial propagation steps:" << prop_steps << endl;
    cout << " Weave Time allowed:" << weave_time << endl;
    cout << "----------------------------------------------------" << endl;
}

void print_bake_off(InvariantMap const& invmap) {
    bool disjoint;
    int r2;

    vector<Location*>::iterator vl;

    for (vl = loclist->begin(); vl < loclist->end(); vl++) {
        r2 = 0;
        disjoint = true;

        string const& what = (*vl)->get_name();
        C_Polyhedron& loc_inv = (*vl)->invariant_reference();
        C_Polyhedron const& other_inv = invmap(what);

        cout << "Location :" << what << " ";

        // Am I stronger
        if (other_inv.contains(loc_inv)) {
            r2++;  // I am one up
            disjoint = false;
        }
        // Is the other_inv stronger?

        if (loc_inv.contains(other_inv)) {
            r2--;
            disjoint = false;
        }

        if (disjoint) {
            cout << "Disjoint" << endl;
        } else if (r2 > 0) {
            cout << " + " << endl;
        } else if (r2 < 0) {
            cout << " - " << endl;
        } else if (r2 == 0) {
            cout << " == " << endl;
        } else {
            // this is unreachable (or is it? :-)
            cout << " <<Unknown Relation>>" << endl;
        }
    }
}

void check_invariant_ok() {
    cout << endl << "> > > In check_invariant_ok()";
    cerr << "Checking for invariant..." << endl;
    vector<TransitionRelation*>::iterator vi;
    for (vi = trlist->begin(); vi != trlist->end(); ++vi) {
        (*vi)->check_map();
    }
    cerr << "Done!" << endl;
    cout << endl << "< < < Out of check_invariant_ok()";
}
