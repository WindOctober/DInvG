
#include <iostream>
#include <regex>
#include <string>
#include <vector>
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
int debug;
int debug_2;
int debug_3;
int num_context;
bool print_tree;
bool zero;
bool one;
bool falsepath;
bool trsat;
bool noexitpath;
bool djinv;
bool arrinv;
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
int* tt;
C_Polyhedron* invd;

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
Counter counter;
bool search_location(char* w, Location** m);
bool search_transition_relation(char* w, TransitionRelation** m);
int find_variable(char* what);
void add_preloc_invariants_to_transitions();
void print_status();
void print_bake_off(InvariantMap const& what);

void check_invariant_ok();
void Scan_Input();


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

int find_variable(char* what) {
    int i = f->search(what);
    if (i == VAR_NOT_FOUND) {
        string x = string("Error:: Variable ") + what + string(" not found");
        exit(1);
    }

    return i;
}

bool search_location(char* name, Location** what) {
    vector<Location*>::iterator vi;
    string nstr(name);
    for (vi = loclist->begin(); vi < loclist->end(); vi++) {
        if ((*vi)->matches(nstr)) {
            *what = (*vi);
            return true;
        }
    }

    return false;
}

bool search_transition_relation(char* name, TransitionRelation** what) {
    vector<TransitionRelation*>::iterator vi;
    string nstr(name);
    for (vi = trlist->begin(); vi < trlist->end(); vi++) {
        if ((*vi)->matches(nstr)) {
            *what = (*vi);
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
    if (strcmp(x, "one") == 0)
        return ONECONTEXT;
    if (strcmp(x, "many") == 0)
        return MANYCONTEXT;
    if (strcmp(x, "new_many") == 0)
        return NEW_MANYCONTEXT;
    if (strcmp(x, "new_2_many") == 0)
        return NEW_2_MANYCONTEXT;
    if (strcmp(x, "new_3_many") == 0)
        return NEW_3_MANYCONTEXT;
    if (strcmp(x, "newdfs") == 0)
        return NEWDFS;
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
    if (strcmp(x, "noinst") == 0)
        return NO_INSTANTIATION;
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

void collect_invariants_for_initial_by_eliminating(C_Polyhedron& cpoly,
                                                   C_Polyhedron& invd) {
    //
    //  Collect invariants for initial
    //
    vector<Location*>::iterator vl;
    int loclist_size = loclist->size();
    invd = C_Polyhedron(fd->get_dimension(), UNIVERSE);
    vl = loclist->begin();

    //    Firstly, collect invariants for initial location by eliminating
    //      for initial *vl, i.e. location,
    //      use cpoly to update *vl->invariant and *vl->invariant updates invd.
    // for (vl=loclist->begin(); vl!=loclist->end(); vl++)
    (*vl)->extract_invariants_and_update_for_one_location_by_eliminating(cpoly,
                                                                         invd);
    /*
    //  Recursive Propagation
    //    Secondly, build the invariants from initial location by propagation
    int propagation_flag[loclist_size]={0};
    propagation_flag[0]=1;
    int i = 0;
    for ( vl = loclist->begin(); vl < loclist->end(); vl++ ){// propagate from
    i-th location for (int j=0; j<loclist_size; j++){ if (propagation_flag[j] ==
    0){// the location without invariants needs to propagate if (
    !location_matrix[i][j].empty() ){// find the non-empty vector of
    location_matrix cout<<endl<<"Location "<<(*loclist)[j]->get_name()<<" at
    Propagation:";
            //  prepare the consatraints
            C_Polyhedron loc_i_inv = (*loclist)[i]->get_invariant();
            int trans_index = location_matrix[i][j][0];
            C_Polyhedron trans_relation =
    (*trlist)[trans_index]->get_relation(); cout<<endl<<"From Location invariant
    "<<(*loclist)[i]->get_name()<<endl<<"   "<<loc_i_inv; cout<<endl<<"Through
    Transition relation "<<(*trlist)[trans_index]->get_name()<<": "<<endl<<"
    "<<trans_relation;

            //  Propagation
            (*loclist)[j]->propagate_invariants_and_update_for_except_initial_by_propagation(loc_i_inv,
    trans_relation);
            //    Contains Test
            (*loclist)[j]->contains_test(cpoly, loc_i_inv, trans_relation);

            //  make flag for location has been added invariants
            propagation_flag[j]=1;
          }
        }
      }
      i++;
    }
    */
    return;
}

void collect_invariants_for_except_initial_by_propagation() {
    //
    //  Collect invariants for except initial
    //
    vector<Location*>::iterator vl;
    int loclist_size = loclist->size();
    cout << endl
         << "> > > collect_invariants_for_except_initial_by_propagation()";

    //    Secondly, build the invariants from initial location by propagation
    int propagation_flag[loclist_size] = {0};
    propagation_flag[0] = 1;
    int i = 0;
    for (vl = loclist->begin(); vl < loclist->end();
         vl++) {  // propagate from i-th location
        //  The "int i" is the index of loclist,
        //  we just use vl = loclist->begin() to count for intuition
        //  but actually use "int i" to count in following index
        for (int j = 0; j < loclist_size; j++) {
            if (propagation_flag[j] ==
                0) {  // the location without invariants needs to propagate
                if (!location_matrix[i][j]
                         .empty()) {  // find the non-empty vector of
                                      // location_matrix
                    cout << endl
                         << "Location " << (*loclist)[j]->get_name()
                         << " at Propagation:";

                    //  prepare the constraints for location invariant and
                    //  transition relation
                    C_Polyhedron loc_i_inv = (*loclist)[i]->get_invariant();
                    for (vector<int>::iterator trans_index =
                             location_matrix[i][j].begin();
                         trans_index < location_matrix[i][j].end();
                         trans_index++) {
                        C_Polyhedron trans_relation =
                            (*trlist)[*trans_index]->get_relation();
                        cout << endl
                             << "From Location invariant "
                             << (*loclist)[i]->get_name() << endl
                             << "   " << loc_i_inv;
                        cout << endl
                             << "Through Transition relation "
                             << (*trlist)[*trans_index]->get_name() << ": "
                             << endl
                             << "   " << trans_relation;

                        //  Propagation
                        (*loclist)[j]
                            ->propagate_invariants_and_update_for_except_initial_by_propagation(
                                loc_i_inv, trans_relation);
                        //    Contains Test
                        //(*loclist)[j]->contains_test(cpoly, loc_i_inv,
                        //trans_relation);
                    }
                    /*
                    int trans_index = location_matrix[i][j][0];
                    C_Polyhedron trans_relation =
                    (*trlist)[trans_index]->get_relation(); cout<<endl<<"From
                    Location invariant "<<(*loclist)[i]->get_name()<<endl<<"
                    "<<loc_i_inv; cout<<endl<<"Through Transition relation
                    "<<(*trlist)[trans_index]->get_name()<<": "<<endl<<"
                    "<<trans_relation;

                    //  Propagation
                    (*loclist)[j]->propagate_invariants_and_update_for_except_initial_by_propagation(loc_i_inv,
                    trans_relation);
                    //    Contains Test
                    //(*loclist)[j]->contains_test(cpoly, loc_i_inv,
                    trans_relation);
                    */

                    //  make flag for location has been added invariants
                    propagation_flag[j] = 1;
                }
            }
        }
        i++;
    }

    return;
}

void collect_invariants_for_initial_by_recursive_eliminating(
    C_Polyhedron& cpoly,
    C_Polyhedron& invd) {
    /*
     *  Collect invariants
     */
    vector<Location*>::iterator vl;
    invd = C_Polyhedron(fd->get_dimension(), UNIVERSE);

    //    Firstly, collect invariants for initial location by recursive
    //    eliminating
    vl = loclist->begin();
    (*vl)->extract_invariants_and_update_for_initial_by_recursive_eliminating(
        cpoly, invd);

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

void binary_eliminating(C_Polyhedron& cpoly, C_Polyhedron& invd) {
    // cout<<endl<<"7.get here?";
    cout << endl
         << "(int)(cpoly.space_dimension()) :"
         << (int)(cpoly.space_dimension());
    cout << endl
         << "( (*loclist)[0]->get_dimension()+1 ) : "
         << ((*loclist)[0]->get_dimension() + 1);
    if ((int)(cpoly.space_dimension()) ==
        ((*loclist)[0]->get_dimension() + 1)) {
        // cout<<endl<<"8.get here?";
        (*loclist)[global_binary_i]
            ->extract_invariants_and_update_by_binary_eliminating(cpoly, invd);
        global_binary_i++;
        cout << endl << "global_binary_i : " << global_binary_i;
        return;
    }
    // cout<<endl<<"9.get here?";

    C_Polyhedron p_left = cpoly;
    C_Polyhedron p_right = cpoly;
    C_Polyhedron* cpoly_left =
        new C_Polyhedron(cpoly.space_dimension(), UNIVERSE);
    *cpoly_left = p_left;
    C_Polyhedron* cpoly_right =
        new C_Polyhedron(cpoly.space_dimension(), UNIVERSE);
    //*cpoly_right = swap2_index_and_divide_from(cpoly,
    //cpoly.space_dimension()/2);
    *cpoly_right = p_right;
    // cout<<endl<<"1.get here?";

    int l = 0;
    int m = cpoly.space_dimension() / 2;
    int h = cpoly.space_dimension();
    Project_by_Kohler(*cpoly_left, l, m);
    Project_by_Kohler(*cpoly_right, m, h);
    // cout<<endl<<"2.get here?";

    binary_eliminating(*cpoly_left, invd);
    // cout<<endl<<"3.get here?";
    delete (cpoly_left);
    // cout<<endl<<"4.get here?";
    binary_eliminating(*cpoly_right, invd);
    // cout<<endl<<"5.get here?";
    delete (cpoly_right);
    // cout<<endl<<"6.get here?";

    return;
}

void collect_invariants_by_binary_eliminating(C_Polyhedron& cpoly,
                                              C_Polyhedron& invd) {
    /*
     *  Collect invariants
     */
    vector<Location*>::iterator vl;
    invd = C_Polyhedron(fd->get_dimension(), UNIVERSE);

    //    Firstly, collect invariants for initial location by recursive
    //    eliminating
    // vl = loclist->begin();
    //(*vl)->extract_invariants_and_update_for_initial_by_recursive_eliminating(cpoly,invd);

    binary_eliminating(cpoly, invd);
    global_binary_i = 0;

    return;
}

void dfs_traverse_recursive(int depth,
                            vector<Clump>& vcl,
                            C_Polyhedron& cpoly,
                            C_Polyhedron& invd) {
    /*
    cout<<endl;
    cout<<endl<<"  "<<"depth "<<depth;
    cout<<endl<<"  "<<"invd is ";
    cout<<endl<<"    "<<invd;
    cout<<endl<<"  "<<"cpoly is ";
    cout<<endl<<"    "<<cpoly;
    cout<<endl<<"  "<<"invd contains cpoly ? ";
    */
    // cout<<endl<<"depth:"<<depth<<", cpoly:";
    // cout<<endl<<cpoly;

    if (invd.contains(cpoly)) {
        bang_count++;
        // cout<<"banged";
        return;
    }

    if (depth == 0) {
        weave_count++;
        cout << endl << "/-----------------------------";
        collect_timer.restart();
        collect_invariants(cpoly, invd);
        cout << endl << "- Have Collected " << weave_count << " invariant(s) ";
        collect_timer.stop();
        cout << endl
             << "- The collect_invariants Time Taken (0.01s) = "
             << collect_timer.compute_time_elapsed() << endl;
        collect_time = collect_time + collect_timer.compute_time_elapsed();
        cout << endl << "\\-----------------------------" << endl;
        //    prune_clumps(vcl);
        return;
    }

    if (weave_timer.compute_time_elapsed() >= weave_time) {
        cout << "Time is up!" << endl;
        return;
    }

    vcl[depth - 1].clear();
    while (vcl[depth - 1].has_next()) {
        // cout<<endl<<"in while...next()";
        // cout<<endl<<"depth:"<<depth<<", cpoly:";
        // cout<<endl<<cpoly;
        // cout<<endl<<"vcl["<<depth-1<<"].size():"<<vcl[depth-1].get_count();
        C_Polyhedron p(cpoly);
        // Timer test_time_for_intersection;
        p.intersection_assign(vcl[depth - 1].get_reference());
        // test_time_for_intersection.stop();
        // cout<<endl<<"- Intersection Time Taken (0.01s) =
        // "<<test_time_for_intersection.compute_time_elapsed()<<endl;

        dfs_traverse_recursive(depth - 1, vcl, p, invd);

        vcl[depth - 1].next();
    }
    return;
}

void dfs_traverse_recursive_for_initial_by_eliminating(int depth,
                                                       vector<Clump>& vcl,
                                                       C_Polyhedron& cpoly,
                                                       C_Polyhedron& invd) {
    if (invd.contains(cpoly)) {
        bang_count++;
        return;
    }

    if (depth == 0) {
        weave_count++;
        cout << endl << "/-----------------------------";
        // Timer test_time_for_minimized;
        collect_invariants_for_initial_by_eliminating(cpoly, invd);
        cout << endl << "- Have Collected " << weave_count << " invariant(s)";
        // test_time_for_minimized.stop();
        // cout<<endl<<"- The collect_invariants's function Time Taken (0.01s) =
        // "<<test_time_for_minimized.compute_time_elapsed()<<endl;
        cout << endl << "\\-----------------------------" << endl;
        //    prune_clumps(vcl);
        return;
    }

    if (weave_timer.compute_time_elapsed() >= weave_time) {
        cout << "Time is up!" << endl;
        return;
    }

    vcl[depth - 1].clear();
    while (vcl[depth - 1].has_next()) {
        C_Polyhedron p(cpoly);
        // Timer test_time_for_intersection;
        p.intersection_assign(vcl[depth - 1].get_reference());
        // test_time_for_intersection.stop();
        // cout<<endl<<"- Intersection Time Taken (0.01s) =
        // "<<test_time_for_intersection.compute_time_elapsed()<<endl;

        dfs_traverse_recursive_for_initial_by_eliminating(depth - 1, vcl, p,
                                                          invd);

        vcl[depth - 1].next();
    }
    return;
}

void dfs_traverse_recursive_for_initial_by_recursive_eliminating(
    int depth,
    vector<Clump>& vcl,
    C_Polyhedron& cpoly,
    C_Polyhedron& invd) {
    if (invd.contains(cpoly)) {
        bang_count++;
        return;
    }

    if (depth == 0) {
        weave_count++;
        cout << endl << "/-----------------------------";
        Timer test_time_for_minimized;
        collect_invariants_for_initial_by_recursive_eliminating(cpoly, invd);
        test_time_for_minimized.stop();
        cout << endl
             << "- The collect_invariants's function Time Taken (0.01s) = "
             << test_time_for_minimized.compute_time_elapsed() << endl;
        cout << "\\-----------------------------" << endl;
        //    prune_clumps(vcl);
        return;
    }

    if (weave_timer.compute_time_elapsed() >= weave_time) {
        cout << "Time is up!" << endl;
        return;
    }

    vcl[depth - 1].clear();
    while (vcl[depth - 1].has_next()) {
        C_Polyhedron p(cpoly);
        // Timer test_time_for_intersection;
        p.intersection_assign(vcl[depth - 1].get_reference());
        // test_time_for_intersection.stop();
        // cout<<endl<<"- Intersection Time Taken (0.01s) =
        // "<<test_time_for_intersection.compute_time_elapsed()<<endl;

        dfs_traverse_recursive_for_initial_by_recursive_eliminating(
            depth - 1, vcl, p, invd);

        vcl[depth - 1].next();
    }
    return;
}

void dfs_traverse_recursive_for_binary_eliminating(int depth,
                                                   vector<Clump>& vcl,
                                                   C_Polyhedron& cpoly,
                                                   C_Polyhedron& invd) {
    // Timer test_time_for_contains;
    int contains = invd.contains(cpoly);
    // test_time_for_contains.stop();
    // cout<<endl<<"- The contains function Time Taken (0.01s) =
    // "<<test_time_for_contains.compute_time_elapsed();
    // global_contains_time+=test_time_for_contains.compute_time_elapsed();
    // cout<<endl<<"- The global_contains_time Time Taken (0.01s) =
    // "<<global_contains_time;
    if (contains) {
        bang_count++;
        return;
    }

    if (depth == 0) {
        weave_count++;
        cout << endl << "/-----------------------------";
        // Timer test_time_for_minimized;
        collect_invariants_by_binary_eliminating(cpoly, invd);
        cout << endl << "- Have Collected " << weave_count << " invariant(s) ";
        // test_time_for_minimized.stop();
        // cout<<endl<<"- The collect_invariants's function Time Taken (0.01s) =
        // "<<test_time_for_minimized.compute_time_elapsed()<<endl;
        cout << endl << "\\-----------------------------" << endl;
        //    prune_clumps(vcl);
        return;
    }

    if (weave_timer.compute_time_elapsed() >= weave_time) {
        cout << "Time is up!" << endl;
        return;
    }

    vcl[depth - 1].clear();
    while (vcl[depth - 1].has_next()) {
        C_Polyhedron p(cpoly);
        // Timer test_time_for_intersection;
        p.intersection_assign(vcl[depth - 1].get_reference());
        // test_time_for_intersection.stop();
        // cout<<endl<<"- Intersection Time Taken (0.01s) =
        // "<<test_time_for_intersection.compute_time_elapsed()<<endl;

        dfs_traverse_recursive_for_binary_eliminating(depth - 1, vcl, p, invd);

        vcl[depth - 1].next();
    }
    return;
}

void dfs_traverse_recursive_for_one_location_by_eliminating(
    int target_index,
    int depth,
    Tree& tr,
    C_Polyhedron& cpoly,
    C_Polyhedron& invd) {
    if (invd.contains(cpoly)) {
        // tr.Print_Prune_Tree(depth,"Banged"); // print for debug and improve
        // algorithm
        bang_count++;
        single_bang_count++;
        return;
    }

    if (depth == 0) {
        // backtrack_flag = true;
        weave_count++;
        single_weave_count++;
        cout << endl << endl << "/-----------------------------";
        tr.Print_Prune_Tree(depth,
                            "Weaved");  // print for debug and improve algorithm
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
        cout << endl << "\\-----------------------------" << endl;
        prune_nodes_timer.restart();
        // tr.prune_node_self_inspection(target_index,invd);
        prune_nodes_timer.stop();
        prune_nodes_time += prune_nodes_timer.compute_time_elapsed();
        return;
    }

    if (total_timer.compute_time_elapsed() >= weave_time) {
        cout << "Time is up!" << endl;
        return;
    }

    tr.get_clump(depth - 1).clear();
    while (tr.get_clump(depth - 1).has_next()) {
        C_Polyhedron p(cpoly);
        p.intersection_assign(tr.get_clump(depth - 1).get_reference());

        dfs_traverse_recursive_for_one_location_by_eliminating(
            target_index, depth - 1, tr, p, invd);

        backtrack_timer.restart();  // Timer On
        if (backtrack_flag == true) {
            bool flag = invd.contains(cpoly);
            if (flag) {
                backtrack_success++;
                cout << endl << "Pruned by backtracking in depth " << depth;
                tr.get_clump(depth - 1).clear();
                return;
            } else {
                if (backtrack_success >= 1) {
                    backtrack_count++;
                    backtrack_success = 0;
                }
                backtrack_flag = false;
            }
        }
        backtrack_timer.stop();  // Timer Off
        backtrack_time += backtrack_timer.compute_time_elapsed();

        // For prune_node_self_inspection
        if (depth - 1 < tr.get_first_conflict()) {
            return;
        } else if (depth - 1 == tr.get_first_conflict()) {
            tr.clear_first_conflict();
            backhere_flag = true;
        }

        if (backhere_flag == false) {
            tr.get_clump(depth - 1).next();
        } else {
            backhere_flag = false;
        }
    }
    return;
}

void dfs_traverse(vector<Clump>& vcl, C_Polyhedron& initp) {
    // first find out the number of clumps
    // a polyhedron containing the solutions contained to date
    // initiate a dfs traversal.
    // write an invariant extraction function at depth 0

    C_Polyhedron invd(*trivial);
    int ncl = 0;
    vector<Clump>::iterator vi;
    for (vi = vcl.begin(); vi < vcl.end(); vi++) {
        ncl++;
        (*vi).clear();
    }

    weave_timer.restart();

    /***/
    // modified and needed be deleted
    // cout<<endl<<"test and set 'ncl'=? ";
    // ncl=0;
    // vector<Clump> test_vcl = vcl;
    // test_vcl[0] = vcl[3];
    /***/

    dfs_traverse_recursive(ncl, vcl, initp, invd);
}

void dfs_traverse_for_initial_by_eliminating(vector<Clump>& vcl,
                                             C_Polyhedron& initp) {
    // Here is the function of "extract_invariant_by_eliminating()"
    C_Polyhedron invd(*trivial);
    int ncl = 0;
    vector<Clump>::iterator vi;
    for (vi = vcl.begin(); vi < vcl.end(); vi++) {
        ncl++;
        (*vi).clear();
    }
    weave_timer.restart();

    dfs_traverse_recursive_for_initial_by_eliminating(ncl, vcl, initp, invd);
}

void dfs_traverse_for_initial_by_recursive_eliminating(vector<Clump>& vcl,
                                                       C_Polyhedron& initp) {
    // Here is the function of "extract_invariant_by_eliminating()"
    C_Polyhedron invd(*trivial);
    int ncl = 0;
    vector<Clump>::iterator vi;
    for (vi = vcl.begin(); vi < vcl.end(); vi++) {
        ncl++;
        (*vi).clear();
    }
    weave_timer.restart();

    dfs_traverse_recursive_for_initial_by_recursive_eliminating(ncl, vcl, initp,
                                                                invd);
}

void dfs_traverse_for_binary_eliminating(vector<Clump>& vcl,
                                         C_Polyhedron& initp) {
    // Here is the function of "extract_invariant_by_eliminating()"
    C_Polyhedron invd(*trivial);
    int ncl = 0;
    vector<Clump>::iterator vi;
    for (vi = vcl.begin(); vi < vcl.end(); vi++) {
        ncl++;
        (*vi).clear();
    }
    weave_timer.restart();

    dfs_traverse_recursive_for_binary_eliminating(ncl, vcl, initp, invd);
}

void dfs_traverse_for_one_location_by_eliminating(int target_index,
                                                  vector<Clump>& vcl,
                                                  C_Polyhedron& initp) {
    C_Polyhedron invd(*trivial);
    Tree tr = Tree();  // empty tree
    tr.set_target_index(target_index);
    int ncl = 0;
    vector<Clump>::iterator vi;
    for (vi = vcl.begin(); vi < vcl.end(); vi++) {
        ncl++;
        (*vi).clear();
    }

    cout << endl
         << endl
         << "/ Start to solve Location "
         << (*loclist)[target_index]->get_name();
    if (tree_prior == "target_prior1") {
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

    // tr.prune_clumps_by_hierarchy_inclusion();

    dfs_traverse_recursive_for_one_location_by_eliminating(target_index, ncl,
                                                           tr, initp, invd);
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
    num_context = 8;
    projection = "kohler_improvement_eliminate_c";
    tree_prior = "target_prior2";
    some_per_group = "two_per_group";
    gendrop = false;
    global_sub_system_list = new vector<System*>();
    zero = one = true;
    falsepath = true;
    trsat = true;
    noexitpath = true;
    djinv = true;
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
        case 7:
            cout << "newdfs_sequences" << endl;
            break;
        case 8:
            cout << "newdfs_seq_propagation" << endl;
            break;
        default:
            cout << endl;
            break;
    }


    if (num_context == 7) {
        cout << "| DFS Search method : " << tree_prior << endl;
        cout << "| Sequences Divide method : " << some_per_group << endl;
        cout << "| Projection method : " << projection << endl;
    }

    if (num_context == 8) {
        cout << "| DFS Search method : " << tree_prior << endl;
        cout << "| Sequences Divide method : " << some_per_group << endl;
        cout << "| Projection method : " << projection << endl;
    }

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
	return -1;
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
	return -1;
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
    cout;
    cout << endl << "/----------------------------- ";
    cout << endl << "| Adjacency Matrix for Location and Transition: ";
    cout << endl << "----------------------------- ";
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

int main(int argc, char* argv[]) {
    ios::sync_with_stdio(false);
    total_timer.restart();
    Initialize_before_Parser();
    Scan_Input();
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
    tt = new int[fm->get_dimension()];

    if (num_context == 7) {
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

    } 
    else if (num_context == 8) {
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

    }  //    eocse if (num_context == 8)
    total_timer.stop();
    Print_Location();
    if (djinv) {
        print_disjunctive_inv_before_program();
    }
    if (arrinv) {
        print_array_inv_before_program();
    }
    Print_Status_after_Solver();
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
            r2--;  // h79 is one up
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

void Scan_Input() {
    cout << endl << "- Parsing Input Doing...";

    cout << endl << "Get Input Variable...\n";
    smatch match;
    string line;
    int stage = -1;  // Variable Reading.
    f = new var_info();
    regex trans_pattern(R"((Transition|transition)\s+(\w+):\s*(\w+)\s*,\s*(\w+)\s*,\s*)");
    regex self_trans_pattern(R"((Transition|transition)\s+(\w+)\s*:\s*(\w+)\s*,\s*)");
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
	Location* invariant_location =NULL;
    C_Polyhedron* new_poly = NULL;
    TransitionRelation* new_transition = NULL;
	bool test=false;
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
                f->search_and_insert(token.c_str());
            }
            continue;
        }
        if (stage == 1 || stage == 2) {
            if (line.find("end") != string::npos) {
                if (new_transition && new_poly) {
                    new_transition->set_relation(new_poly);
                }
				Location* rec;
                return;
            }
            if (regex_match(line, match, loc_pattern)) {
                if (new_poly && new_location) {
                    new_location->set_polyhedron(new_poly);
                }
                if (new_poly && new_transition) {
                    new_transition->set_relation(new_poly);
                }
				if (new_poly && invariant_location){
					invariant_location->set_invariant_polyhedron(new_poly);
				}
                new_poly = NULL;
				new_location = NULL;
				invariant_location=NULL;
                new_transition = NULL;
                string loc_name = match[2];
                // cout<<loc_name<<" "<<loc_name.length()<<" "<<token<<endl;
                if (!search_location((char*)loc_name.c_str(), &new_location)) {
                    new_location =
                        new Location(f->get_dimension(), f, fd, fm, loc_name);
                    loclist->push_back(new_location);
                } else {
                    cerr << "[ERROR] Multi-defined Location." << endl;
                    exit(1);
                }
            } else if (regex_match(line, match, trans_pattern) ||
                       regex_match(line, match, self_trans_pattern)) {
				test=false;
                stage = 2;
                if (new_poly && new_location) {
                    new_location->set_polyhedron(new_poly);
                }
                if (new_poly && new_transition) {
                    new_transition->set_relation(new_poly);
                }
				if (new_poly && invariant_location){
					invariant_location->set_invariant_polyhedron(new_poly);
				}
                new_poly = NULL;
				new_location = NULL;
				invariant_location=NULL;
                new_transition = NULL;
                string transition_name = match[2];
                string loc_name_start = match[3];
				Location* loc_end;
				Location* loc_start;
				// cout<<endl;
				if (!search_transition_relation((char*)transition_name.c_str(),
                                                &new_transition)) {
                    new_transition = new TransitionRelation(
                        f->get_dimension(), f, fd, fm, transition_name);
                    trlist->push_back(new_transition);
                } else {
                    cerr << "[ERROR] Multi-defined Transition." << endl;
                    exit(1);
                }
                if (!search_location((char*)loc_name_start.c_str(),
                                     &loc_start)) {
                    cerr << "[ERROR] Transition use undefined location" << endl;
                    exit(1);
                }
                if (regex_match(line, match, trans_pattern)) {
                    string loc_name_end = match[4];
                    if (!search_location((char*)loc_name_end.c_str(),
                                         &loc_end)) {
                        cerr << "[ERROR] Transition use undefined location"
                             << endl;
                        exit(1);
                    }
					new_transition->set_locs(loc_start, loc_end);
                }
				else{
					new_transition->set_locs(loc_start, loc_start);
				}
                // cout<<transition_name<<" "<<loc_name_start<<"
                // "<<loc_name_end<<endl;
                
                
            } 
			else if (regex_match(line, match, invariant_pattern)){
				if (new_poly && new_location) {
                    new_location->set_polyhedron(new_poly);
                }
                if (new_poly && new_transition) {
                    new_transition->set_relation(new_poly);
                }
				if (new_poly && invariant_location){
					invariant_location->set_invariant_polyhedron(new_poly);
				}
                new_poly = NULL;
				new_location = NULL;
				invariant_location=NULL;
                new_transition = NULL;
                string loc_name = match[2];
                // cout<<loc_name<<" "<<loc_name.length()<<" "<<token<<endl;
                if (!search_location((char*)loc_name.c_str(), &invariant_location)) {
                    cerr << "[ERROR] undefined Invariant Location." << endl;
                    exit(1);
                }
			}
			else {
                if (!new_poly) {
                    if (stage == 1)
                        new_poly =
                            new C_Polyhedron(f->get_dimension(), UNIVERSE);
                    else
                        new_poly =
                            new C_Polyhedron(2 * f->get_dimension(), UNIVERSE);
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
				bool empty=false;
                while (it != end) {
                    string term = it->str();
                    if (regex_match(term, match, primed_coef_var_pattern)) {
                        int coef = stoi(match[1]);
                        if (is_negative)
                            coef = -coef;
                        string var = match[2];
                        int index = f->search(var.c_str());
                        if (index == VAR_NOT_FOUND) {
                            cout << "[ERROR] Undefined variable " << var
                                 << endl;
                            exit(1);
                        }
                        Linear_Expression* res = new Linear_Expression(
                            abs(coef) * Variable(index + f->get_dimension()));
                        if (!is_rhs){
							if (coef>0)
								(*le) += (*res);
							else
								(*le) -= (*res);
						}
                        else{
							if (coef>0)
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
                        int index = f->search(var.c_str());
                        if (index == VAR_NOT_FOUND) {
                            cout << "[ERROR] Undefined variable " << var
                                 << endl;
                            exit(1);
                        }
                        Linear_Expression* res =
                            new Linear_Expression(abs(coef) * Variable(index));
                        if (!is_rhs){
							if (coef>0)
								(*le) += (*res);
							else
								(*le) -= (*res);
						}
                        else{
							if (coef>0)
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
                        Linear_Expression* res = new Linear_Expression(abs(coef));
                        if (!is_rhs){
							if (coef>0)
								(*le) += (*res);
							else
								(*le) -= (*res);
						}
                        else{
							if (coef>0)
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

                        int index = f->search(var.c_str());
                        if (index == VAR_NOT_FOUND) {
                            cout << "[ERROR] Undefined variable " << var
                                 << endl;
                            exit(1);
                        }
                        Linear_Expression* res = new Linear_Expression(
                            abs(coef) * Variable(index + f->get_dimension()));
                        if (!is_rhs){
							if (coef>0)
								(*le) += (*res);
							else
								(*le) -= (*res);
						}
                        else{
							if (coef>0)
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

                        int index = f->search(var.c_str());
                        if (index == VAR_NOT_FOUND) {
                            cout << "[ERROR] Undefined variable " << var
                                 << endl;
                            exit(1);
                        }
                        Linear_Expression* res =
                            new Linear_Expression(abs(coef) * Variable(index));
                        if (!is_rhs){
							if (coef>0)
								(*le) += (*res);
							else
								(*le) -= (*res);
						}
                        else{
							if (coef>0)
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
						is_negative=false;
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
				Linear_Expression* new_le=new Linear_Expression();
				// cout<<*le<<" "<<*right<<endl;
                if (op == 2) {
                    new_constraint = new Constraint((*le) >= (*right));
                } else if (op == 1) {
                    new_constraint = new Constraint((*le) <= (*right));
                } else {
                    new_constraint = new Constraint((*le) == (*right));
                }
                new_poly->add_constraint(*new_constraint);
				// if (test)
				// 	new_constraint->ascii_dump();
				// cout<<*new_constraint<<endl;
				// cout<<"note here!!!!!!!!!!!!!!!"<<endl;
                delete (le);
                delete (right);
                delete (new_constraint);
            }
            continue;
        }
    }
    dimension = f->get_dimension();
    exit(0);
}