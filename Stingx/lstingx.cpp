// DONE: return the final disjunctive invariant to the Frontend.
#include <iostream>
#include <regex>
#include <string>
#include <vector>
#include "Elimination.h"
#include "parser.h"
#include "Location.h"
#include "PolyUtils.h"
#include "LinTS.h"
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
string treePrior;
string some_per_group;
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
bool backtrack_flag;
int prune_count;
int clump_prune_count;
int context_count;
int merge_count;
int bang_count_in_merge;
Counter counter;
void addPreInvtoTrans();
void print_status();

void check_invariant_ok();
// void ScanInput();

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

void collectInv(int index, C_Polyhedron& cpoly, C_Polyhedron& invCoefPoly) {
    invCoefPoly = C_Polyhedron(coefInfo->getDim(), UNIVERSE);
    locList[index]->ExtractAndUpdateInv(cpoly, invCoefPoly);
    return;
}

vector<vector<vector<int>>> GenerateSequences(int index,
                                              vector<Clump>& clumps,
                                              C_Polyhedron& initPoly) {
    Tree tr = Tree();
    tr.setCurId(index);

    for (auto it = clumps.begin(); it < clumps.end(); it++) {
        (*it).resetIter();
    }

    cout << endl
         << "/ Start to solve Location " << locList[index]->getName();

    tr.setPriorClumps(clumps);

    tr.setMaxPolyNum();

    cout << endl << "/ Generate Sequences";
    vector<vector<vector<int>>> sequences;
    sequences = tr.seqGen(some_per_group, initPoly);
    return sequences;
}

void TraverseSequences(vector<vector<vector<int>>> sequences,
                       int index,
                       vector<Clump>& clumps,
                       C_Polyhedron& initPoly) {
    C_Polyhedron invCoefPoly(*trivial);
    Tree tr = Tree();
    tr.setCurId(index);
    vector<Clump>::iterator it;
    for (it = clumps.begin(); it < clumps.end(); it++) {
        (*it).resetIter();
    }

    cout << endl
         << endl
         << "/ Start to solve Location " << locList[index]->getName();

    tr.setPriorClumps(clumps);
    tr.setMaxPolyNum();
    cout << endl << "/ Read(Traverse) Sequences";
    tr.treeSeqTraverse(sequences, initPoly, invCoefPoly);
}

void Initialize() {
    cout << endl << "- Initialize doing...";
    totalSuccessCnt = totalPrunedCnt = backtrack_count = 0;
    backtrack_success = 0;
    backtrack_flag = false;
    merge_count = 0;
    inv_check = false;
    clump_prune_count = prune_count = 0;
    context_count = 0;
    lambdaInfo = new var_info();
    coefInfo = new var_info();
    print_tree = true;
    projection = "kohler_improvement_eliminate_c";
    treePrior = "target_prior2";
    some_per_group = "two_per_group";
    gendrop = false;
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


void PrintStatusBeforeSolving() {
    cout << endl;
    cout << "/----------------------------- " << endl;
    cout << "| Status before Solver: " << endl;
    cout << "----------------------------- " << endl;
    cout << "| Print Tree : " << print_tree << endl;
    cout << "| DFS Search method : " << treePrior << endl;
    cout << "| Sequences Divide method : " << some_per_group << endl;
    cout << "| Projection method : " << projection << endl;
    cout << "| Local invariants to be generated : " << zero << endl;
    cout << "| Increasing invariants to be generated : " << one << endl;
    cout << "| Falsepath to be enabled : " << falsepath << endl;
    cout << "| Exit-Transition is computed : " << (!noexitpath) << endl;
    cout << "| Display Disjunctive Invariants : " << djinv << endl;
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

int getLocIndex(string locName) {
    int i = 0;
    for (auto it = locList.begin(); it < locList.end(); it++) {
        if ((*it)->getName() == locName) {
            return i;
        }
        i++;
    }
    return -1;
}

int getTransIndex(string name) {
    int i = 0;
    for (auto it = transList.begin(); it < transList.end(); it++) {
        if ((*it)->getName() == name) {
            return i;
        }
        i++;
    }
    return -1;
}


void ResetLocInv() {
    for (auto it = locList.begin(); it < locList.end(); it++) {
        cout << endl
             << "- Location " << (*it)->getName() << ": initialize invariant";
        (*it)->initInv();
    }
}

void ComputeProgramInv();

#ifdef USE_LSTINGX_MAIN
int main() {
    ios::sync_with_stdio(false);
    LinTS* root=new LinTS();
    Initialize();
    int parserResult=yyparse(root);
    tt = new int[lambdaInfo->getDim()];
    root->PrintLinTS(1);
    root->ComputeLinTSInv();
    root->PrintInv();
    addPreInvtoTrans();
    PrintStatusBeforeSolving();
    

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
    for (it = transList.begin(); it < transList.end(); ++it) {
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
    for (it = transList.begin(); it != transList.end(); ++it) {
        (*it)->check_map();
    }
    cerr << "Done!" << endl;
    cout << endl << "< < < Out of check_invariant_ok()";
}