// DONE: return the final disjunctive invariant to the Frontend.
#include <iostream>
#include <regex>
#include <string>
#include <vector>
#include "Elimination.h"
#include "Location.h"
#include "PolyUtils.h"
#include "Propagation.h"
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
vector<Location*>* locList;
vector<TransitionRelation*>* transList;
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
bool searchLoc(char* w, Location** m);
bool searchTransRel(char* w, TransitionRelation** m);
void addPreInvtoTrans();
void print_status();

void check_invariant_ok();
void ScanInput();

bool searchLoc(char* name, Location** what) {
    vector<Location*>::iterator it;
    string nstr(name);
    for (it = locList->begin(); it < locList->end(); it++) {
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

void collectInv(int index, C_Polyhedron& cpoly, C_Polyhedron& invCoefPoly) {
    invCoefPoly = C_Polyhedron(coefInfo->getDim(), UNIVERSE);
    (*locList)[index]->ExtractAndUpdateInv(cpoly, invCoefPoly);
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
         << "/ Start to solve Location " << (*locList)[index]->getName();

    tr.setPriorClumps(clumps);

    tr.setMaxPolyNum();

    cout << endl << "/ Generate Sequences";
    vector<vector<vector<int>>> sequences;
    sequences = tr.seqGen(some_per_group, initPoly);
    return sequences;
}

void GenerateSequencesIntra(vector<vector<vector<vector<int>>>>& actualSeqs,
                            int index,
                            vector<Clump>& clumps,
                            C_Polyhedron& initPoly) {
    Tree tr = Tree();
    tr.setCurId(index);
    for (auto it = clumps.begin(); it < clumps.end(); it++) {
        (*it).resetIter();
    }
    cout << endl
         << "/ Start to solve Location " << (*locList)[index]->getName();
    tr.setIntraClumps(clumps);
    tr.setMaxPolyNum();

    cout << endl << "/ Generate Sequences";
    vector<vector<vector<int>>> sequences;
    sequences = tr.seqGen("one_per_group", initPoly);
    actualSeqs.push_back(sequences);

    cout << endl << "\\ Generate Sequences";
    cout << endl << "\\ End to solve Location " << (*locList)[index]->getName();
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
         << "/ Start to solve Location " << (*locList)[index]->getName();

    tr.setPriorClumps(clumps);
    tr.setMaxPolyNum();
    cout << endl << "/ Read(Traverse) Sequences";
    tr.treeSeqTraverse(sequences, initPoly, invCoefPoly);
}

void TraverseSequencesIntra(vector<vector<vector<int>>> sequences,
                            int index,
                            vector<Clump>& clumps,
                            C_Polyhedron& initPoly) {
    C_Polyhedron invCoefPoly(*trivial);
    Tree tr = Tree();  // empty tree
    tr.setCurId(index);
    vector<Clump>::iterator it;
    for (it = clumps.begin(); it < clumps.end(); it++) {
        (*it).resetIter();
    }
    cout << endl
         << endl
         << "/ Start to solve Location " << (*locList)[index]->getName();
    // extract only-one-clumps which is intra-transition about this location
    tr.setIntraClumps(clumps);
    tr.setMaxPolyNum();
    cout << endl << "/ Read(Traverse) Sequences";
    tr.treeSeqTraverse(sequences, initPoly, invCoefPoly);

    cout << endl << "\\ Read(Traverse) Sequences";
    cout << endl << "\\ End to solve Location " << (*locList)[index]->getName();
}

// compute invariants by farkas for this one location from intra-transition
void collectInvIntra(vector<Clump>& clumps, int locId) {
    vector<vector<vector<vector<int>>>> actualSeqs;
    int coefNum = coefInfo->getDim();
    C_Polyhedron initPoly(coefNum, UNIVERSE);

    counter.set_location_index_and_init_depth(locId, clumps.size());
    // compute invariants by using initial-value and intra-transition
    bool initLocFlag = (*locList)[locId]->isInitLoc();
    if (!initLocFlag) {
        cout << endl
             << "- ( !initLocFlag ) in Location::"
             << (*locList)[locId]->getName();
        vector<vector<vector<int>>> emptySeq;
        actualSeqs.push_back(emptySeq);
    } else {
        (*locList)[locId]->ComputeCoefConstraints(initPoly);
        GenerateSequencesIntra(actualSeqs, locId, clumps, initPoly);
    }

    /*
     * Read Sequences
     */
    // compute invariants by using initial-value and intra-transition
    if (!initLocFlag) {
        cout << endl
             << "- ( !initLocFlag ) in Location::"
             << (*locList)[locId]->getName();
    } else {
        vector<vector<vector<int>>> sequences;
        if (actualSeqs.size() == 1) {
            sequences = actualSeqs[0];
        } else {
            cout << endl << "Error: There are more than one sequences";
        }
        TraverseSequencesIntra(sequences, locId, clumps, initPoly);
    }

    return;
}

void Initialize_before_Parser() {
    cout << endl << "- Initialize_before_Parser doing...";
    totalSuccessCnt = totalPrunedCnt = backtrack_count = 0;
    backtrack_success = 0;
    backtrack_flag = false;
    merge_count = 0;
    inv_check = false;
    clump_prune_count = prune_count = 0;
    context_count = 0;
    lambdaInfo = new var_info();
    coefInfo = new var_info();
    locList = new vector<Location*>();
    transList = new vector<TransitionRelation*>();
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

void Initialize() {
    cout << endl << "- Initialize_before_Parser doing...";
    totalSuccessCnt = totalPrunedCnt = backtrack_count = 0;
    backtrack_success = 0;
    backtrack_flag = false;
    merge_count = 0;
    inv_check = false;
    clump_prune_count = prune_count = 0;
    context_count = 0;
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
}

void PrintLocsTrans() {
    cout << endl;
    cout << "----------------------------- " << endl;
    cout << "| The Locations read in are: " << endl;
    cout << "----------------------------- " << endl;
    for (vector<Location*>::iterator it = locList->begin(); it < locList->end();
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
    for (vector<Location*>::iterator it = locList->begin(); it < locList->end();
         it++) {
        cout << *(*it);
    }
}

void PrintInvInExitLoc() {
    cout << endl << "/---------------------------------------- ";
    cout << endl << "| Disjunctive Invariants before Program: ";
    cout << endl << "----------------------------------------- ";
    int i = 0;
    for (vector<Location*>::iterator it = locList->begin(); it < locList->end();
         it++) {
        if ((*it)->getName() != EXIT_LOCATION && !(*it)->GetInv().is_empty()) {
            if (i != 0) {
                cout << endl << "\\/";
            }
            print_pure_polyhedron((*it)->GetInv(), (*it)->getInfo());
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
    cout << "| DFS Search method : " << treePrior << endl;
    cout << "| Sequences Divide method : " << some_per_group << endl;
    cout << "| Projection method : " << projection << endl;
    cout << "| Local invariants to be generated : " << zero << endl;
    cout << "| Increasing invariants to be generated : " << one << endl;
    cout << "| Falsepath to be enabled : " << falsepath << endl;
    cout << "| Exit-Transition is computed : " << (!noexitpath) << endl;
    cout << "| Display Disjunctive Invariants : " << djinv << endl;
    cout << "| Display Array Invariants : " << arrinv << endl;
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
    for (auto it = locList->begin(); it < locList->end(); it++) {
        if ((*it)->getName() == locName) {
            return i;
        }
        i++;
    }
    return -1;
}

int getTransIndex(string name) {
    int i = 0;
    for (auto it = transList->begin(); it < transList->end(); it++) {
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
    int locSize = locList->size();
    location_matrix = new vector<int>*[locSize];
    for (int i = 0; i < locSize; i++) {
        location_matrix[i] = new vector<int>[locSize];
    }

    int j = 0, j1 = 0;
    for (auto it = transList->begin(); it < transList->end(); it++) {
        if (!(*it)->getTransRel().is_empty()) {
            location_matrix[getLocIndex((*it)->getPreLocName())]
                           [getLocIndex((*it)->getPostLocName())]
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
    for (int i = 0; i < locSize; i++) {
        cout << endl << "| " << (*locList)[i]->getName() << ": ";
        for (int j = 0; j < locSize; j++) {
            cout << "[";
            for (vector<int>::iterator it = location_matrix[i][j].begin();
                 it < location_matrix[i][j].end(); it++) {
                cout << " " << *it << " ";
            }
            cout << "]->" << (*locList)[j]->getName() << ";  ";
        }
    }
    cout << endl << "----------------------------- ";
    cout << endl << "| Output: " << j1 << " transitions";
    cout << endl << "\\----------------------------- ";
}

void ResetLocInv() {
    for (auto it = locList->begin(); it < locList->end(); it++) {
        cout << endl
             << "- Location " << (*it)->getName() << ": initialize invariant";
        (*it)->initInv();
    }
}

void ComputeProgramInv() {
    Initialize();
    addPreInvtoTrans();
    CreateAdjMat();

    tt = new int[lambdaInfo->getDim()];
    int coefNum = coefInfo->getDim();
    trivial = new C_Polyhedron(coefNum, UNIVERSE);
    for (auto it = locList->begin(); it < locList->end(); it++) {
        (*it)->addTrivial(trivial);
    }

    C_Polyhedron initPoly(coefNum, UNIVERSE);
    for (auto it = locList->begin(); it < locList->end(); it++) {
        (*it)->makeContext();
        (*it)->ComputeCoefConstraints(initPoly);
    }
    vector<Clump> clumps;
    for (auto it = transList->begin(); it < transList->end(); it++) {
        (*it)->ComputeIntraConsecConstraints(clumps);
    }

    for (auto it = locList->begin(); it < locList->end(); it++) {
        (*it)->addClump(clumps);
    }

    int initLocIndex = -1;
    for (int i = 0; i < locList->size(); i++) {
        if ((*locList)[i]->getInitFlag()) {
            initLocIndex = i;
            break;
        }
    }
    if (initLocIndex == -1) {
        cout << endl << "without initial location" << endl;
        exit(-1);
    }

    vector<vector<vector<int>>> actualSeqs;
    counter.set_location_index_and_init_depth(initLocIndex, clumps.size());
    actualSeqs = GenerateSequences(initLocIndex, clumps, initPoly);
    TraverseSequences(actualSeqs, initLocIndex, clumps, initPoly);
    InvPropagation(clumps);
    PrintLocs();
    delete tt;
    delete trivial;
    delete location_matrix;
    return;
}
#ifdef USE_LSTINGX_MAIN
int main() {
    ios::sync_with_stdio(false);
    Initialize_before_Parser();
    ScanInput();
    addPreInvtoTrans();

    PrintStatusBeforeSolving();
    PrintLocsTrans();
    CreateAdjMat();

    tt = new int[lambdaInfo->getDim()];
    int coefNum = coefInfo->getDim();
    trivial = new C_Polyhedron(coefNum, UNIVERSE);
    for (auto it = locList->begin(); it < locList->end(); it++) {
        (*it)->addTrivial(trivial);
    }

    C_Polyhedron initPoly(coefNum, UNIVERSE);
    for (auto it = locList->begin(); it < locList->end(); it++) {
        (*it)->makeContext();
        (*it)->ComputeCoefConstraints(initPoly);
    }
    vector<Clump> clumps;
    for (auto it = transList->begin(); it < transList->end(); it++) {
        (*it)->ComputeIntraConsecConstraints(clumps);
    }

    for (auto it = locList->begin(); it < locList->end(); it++) {
        (*it)->addClump(clumps);
    }

    int initLocIndex = -1;
    for (int i = 0; i < locList->size(); i++) {
        if ((*locList)[i]->getInitFlag()) {
            initLocIndex = i;
            break;
        }
    }
    if (initLocIndex == -1) {
        cout << endl << "without initial location" << endl;
        exit(-1);
    }

    vector<vector<vector<int>>> actualSeqs;
    counter.set_location_index_and_init_depth(initLocIndex, clumps.size());
    actualSeqs = GenerateSequences(initLocIndex, clumps, initPoly);
    TraverseSequences(actualSeqs, initLocIndex, clumps, initPoly);
    InvPropagation(clumps);
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
                    new_location = new Location(info->getDim(), info, coefInfo,
                                                lambdaInfo, locName);
                    locList->push_back(new_location);
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
                    new_transition->set_relation(new_poly);
                }
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
                    new_transition =
                        new TransitionRelation(info->getDim(), info, coefInfo,
                                               lambdaInfo, transition_name);
                    transList->push_back(new_transition);
                } else {
                    cerr << "[ERROR] Multi-defined Transition." << endl;
                    exit(1);
                }
                if (!searchLoc((char*)loc_name_start.c_str(), &loc_start)) {
                    cerr << "[ERROR] Transition use undefined location" << endl;
                    exit(1);
                }
                if (regex_match(line, match, trans_pattern)) {
                    string loc_name_end = match[4];
                    if (!searchLoc((char*)loc_name_end.c_str(), &loc_end)) {
                        cerr << "[ERROR] Transition use undefined location"
                             << endl;
                        exit(1);
                    }
                    new_transition->set_locs(loc_start, loc_end);
                } else {
                    new_transition->set_locs(loc_start, loc_start);
                }
            } else if (regex_match(line, match, invariant_pattern)) {
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
                if (!searchLoc((char*)locName.c_str(), &invariant_location)) {
                    cerr << "[ERROR] undefined Invariant Location." << endl;
                    exit(1);
                }
            } else {
                if (!new_poly) {
                    if (stage == 1)
                        new_poly = new C_Polyhedron(info->getDim(), UNIVERSE);
                    else
                        new_poly =
                            new C_Polyhedron(2 * info->getDim(), UNIVERSE);
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
                            abs(coef) * Variable(index + info->getDim()));
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
                            abs(coef) * Variable(index + info->getDim()));
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