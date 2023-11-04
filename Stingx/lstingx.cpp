// DONE: return the final disjunctive invariant to the Frontend.
#include <iostream>
#include <regex>
#include <string>
#include <vector>
#include "Elimination.h"
#include "LinTS.h"
#include "Location.h"
#include "PolyUtils.h"
#include "TransitionRelation.h"
#include "Tree.h"
#include "parser.h"
#include "ppl.hh"
#include "var-info.h"
using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;
bool gendrop;
int total_time;
string projection;
bool clear_lower_gli = false;
int clear_lower_gli_depth = -1;
bool backhere_flag = false;
int related_location_number;
int related_transition_number;

int global_binary_i = 0;
long int global_contains_time = 0;
vector<int> target_prior;

char err_str[100];
int dimension;
var_info *info, *coefInfo, *lambdaInfo;
vector<Location*> locList;
vector<TransitionRelation*> transList;
Context* glc;  // The global context
vector<Context*>* children;
int* tt;
C_Polyhedron* invCoefPoly;

bool inv_check;
void collect_generators(vector<Context*>* children, Generator_System& g);
int totalSuccessCnt;
int totalPrunedCnt;
int backtrack_count;
int backtrack_success;
int prune_count;
int clump_prune_count;
int context_count;
int merge_count;
int bang_count_in_merge;
Counter counter;
void addPreInvtoTrans();
void check_invariant_ok();

bool searchLoc(char* name, Location** what) {
    vector<Location*>::iterator it;
    string nstr(name);
    for (it = locList.begin(); it < locList.end(); it++) {
        if ((*it)->matches(nstr)) {
            *what = (*it);
            return true;
        }
    }

    return false;
}

void Initialize() {
    cout << endl << "- Initialize doing...";

    merge_count = 0;
    inv_check = false;
    clump_prune_count = prune_count = 0;
    context_count = 0;

    projection = "kohler_improvement_eliminate_c";
    gendrop = false;
    total_time = 360000;
    cout << "Done!" << endl;
}

void Print_Status_after_Solver() {
    cout << endl;
    cout << "/----------------------------- " << endl;
    cout << "| Status after Solver: " << endl;
    cout << "----------------------------- " << endl;
    cout << "| Time Taken Unit: (0.01s)" << endl;
    cout << "| # of Contexts generated = " << context_count << endl;
    cout << "|" << endl;

    cout << "| # of pruned clumps in intra-transition = " << prune_count
         << endl;
    cout << "| # of pruned nodes by self inspection = " << clump_prune_count
         << endl;
    cout << "| # of pruned by backtracking = " << backtrack_count << endl;
    cout << "| # of merged for sub sequences = " << merge_count << endl;
    cout << "|" << endl;

    cout << "| t: collect_invariant Time" << endl;
    cout << "| w: invariants *weav*ed" << endl;

    cout << "| TOTAL: w = " << totalSuccessCnt << endl;
    cout << "|" << endl;

    cout << "| t: dfs_traverse Time" << endl;
    cout << "| b: path *bang*ed" << endl;

    cout << "| TOTAL: b = " << totalPrunedCnt << endl;
    cout << "\\----------------------------- " << endl;
}


void ComputeProgramInv() {
    return;
}

#ifdef USE_LSTINGX_MAIN
int main() {
    ios::sync_with_stdio(false);
    LinTS* root = new LinTS();
    Initialize();
    int parserResult = yyparse(root);
    // TODO : Reimplement the addPreInvtoLoc function within LinTS for testing
    // invariant strengthening techniques.
    // TODO : Consider refining the output before and after the tool runs to
    // make it more visually appealing.
    root->PrintLinTS(1);
    root->ComputeLinTSInv();
    root->PrintInv();
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
    for (it = transList.begin(); it < transList.end(); ++it) {
        (*it)->addPreInv();
    }
    return;
}


void check_invariant_ok() {
    cout << endl << "> > > In check_invariant_ok()";
    cerr << "Checking for invariant..." << endl;
    vector<TransitionRelation*>::iterator it;
    for (it = transList.begin(); it != transList.end(); ++it) {
        (*it)->check_map();
    }
    cerr << "Done!" << endl;
    cout << endl << "< < < Out of check_invariant_ok()";
}