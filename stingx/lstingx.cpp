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
    cout << endl << "- Initialize doing...?...";

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
std::string randomString(size_t length) {
    static const char alphanum[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
    std::string result;
    result.reserve(length);
    for (size_t i = 0; i < length; ++i) {
        result += alphanum[rand() % (sizeof(alphanum) - 1)];
    }
    return result;
}
C_Polyhedron* randomLocPoly(int numVars, int numConstraints) {

    C_Polyhedron* poly = new C_Polyhedron(numVars, Parma_Polyhedra_Library::EMPTY);
    int range = 6;
    int subrange = range / 2;

    while (true) {
        poly = new C_Polyhedron(numVars, Parma_Polyhedra_Library::UNIVERSE);
        for (int i = 0; i < numConstraints; ++i) {
            Linear_Expression expr;
            bool nonZeroX = false;

            int numVarsInConstraint = std::min(rand() % 3 + 1, numVars);
            std::vector<int> selectedVars;
            while (selectedVars.size() < static_cast<size_t>(numVarsInConstraint)) {
                int varIndex = rand() % numVars;
                if (std::find(selectedVars.begin(), selectedVars.end(), varIndex) == selectedVars.end()) {
                    selectedVars.push_back(varIndex);
                }
            }

            for (int var : selectedVars) {
                int coefficient = rand() % range - subrange;
                expr += coefficient * Variable(var);
                nonZeroX = nonZeroX || (coefficient != 0);
            }

            if (!nonZeroX) {
                int nonZeroVar = selectedVars[rand() % selectedVars.size()];
                expr +=  Variable(nonZeroVar);
            }

            int constant = rand() % range - subrange;
            expr += constant;

            if (rand() % 2 == 0) {
                poly->add_constraint(expr <= 0); 
            } else {
                poly->add_constraint(expr == 0);
            }
        }
        if (poly->is_empty()){
            delete poly;
        }
        else break;
    }

    return poly;
}

C_Polyhedron* randomTransPoly(int numVars, int numConstraints) {
    // 使用PPL库的C_Polyhedron类
    C_Polyhedron* poly = new C_Polyhedron(numVars * 2, Parma_Polyhedra_Library::EMPTY);
    int range = 6;
    int subrange = range / 2;

    while (poly->is_empty()) {
        poly = new C_Polyhedron(numVars * 2, Parma_Polyhedra_Library::UNIVERSE);
        for (int i = 0; i < numConstraints; ++i) {
            Linear_Expression expr;
            bool nonZeroX = false;
            bool nonZeroXPrime = false;

            int numVarsInConstraintX = std::min(rand() % 3 + 1, numVars);
            std::vector<int> selectedVarsX;
            while (selectedVarsX.size() < static_cast<size_t>(numVarsInConstraintX)) {
                int varIndex = rand() % numVars;
                if (std::find(selectedVarsX.begin(), selectedVarsX.end(), varIndex) == selectedVarsX.end()) {
                    selectedVarsX.push_back(varIndex);
                }
            }

            for (int var : selectedVarsX) {
                int coefficient = rand() % range - subrange; 
                expr += coefficient * Variable(var);
                nonZeroX = nonZeroX || (coefficient != 0);
            }

            int varIndexPrime = rand() % numVars;
            expr += (rand() % range - subrange) * Variable(numVars + varIndexPrime);
            nonZeroXPrime = true;

            if (!nonZeroX || !nonZeroXPrime) {
                int nonZeroVar = rand() % numVars;
                expr +=  Variable(nonZeroVar);
                expr +=  Variable(numVars + nonZeroVar);
            }

            int constant = rand() % range - subrange;
            expr += constant;

            if (rand() % 2 == 0) {
                poly->add_constraint(expr <= 0); 
            } else {
                poly->add_constraint(expr == 0);
            }
        }
    }

    return poly;
}


void generateRandomLTS(LinTS* lts, int numVars, int numLocations, int numTransitions, int numConstraintsPerTrans) {
    for (int i = 0; i < numVars; ++i) {
        lts->addVariable((char*)randomString(3).c_str());
    }

    std::vector<std::string> locations;
    int init=rand() % numLocations;
    for (int i = 0; i < numLocations; ++i) {
        std::string locName = randomString(4);
        locations.push_back(locName);
        if (i!=init)
            lts->addLocInit((char*)locName.c_str(), nullptr);
        else{
            C_Polyhedron* initialPoly = randomLocPoly(numVars, numConstraintsPerTrans);
            lts->addLocInit((char*)locName.c_str(), initialPoly);
        }
    }
    cout<<"|- Locations generated."<<endl;
    for (int i = 0; i < numTransitions; ++i) {
        std::string transName = randomString(4);
        std::string preLoc = locations[rand() % numLocations];
        std::string postLoc = locations[rand() % numLocations];
        C_Polyhedron* transPoly = randomTransPoly(numVars, numConstraintsPerTrans);
        lts->addTransRel((char*)transName.c_str(), (char*)preLoc.c_str(), (char*)postLoc.c_str(), transPoly);
    }
    cout<<"|- Transitions generated.";
}

void generateSingleCycleLTS(LinTS* lts, int numVars, int numLocations, int numConstraintsPerTrans) {
    for (int i = 0; i < numVars; ++i) {
        lts->addVariable((char*)randomString(3).c_str());
    }

    std::vector<std::string> locations;
    for (int i = 0; i < numLocations; ++i) {
        std::string locName = randomString(4);
        locations.push_back(locName);
    }

    int initIndex = rand() % numLocations;
    std::string initialLoc = locations[initIndex];
    C_Polyhedron* initialPoly = randomLocPoly(numVars, numConstraintsPerTrans);
    lts->addLocInit((char*)initialLoc.c_str(), initialPoly);

    for (int i = 0; i < numLocations; ++i) {
        if (i != initIndex) {
            lts->addLocInit((char*)locations[i].c_str(), nullptr);
        }
    }

    for (int i = 0; i < numLocations; ++i) {
        std::string transName = randomString(4);
        std::string preLoc = locations[i];
        std::string postLoc = locations[(i + 1) % numLocations];
        C_Polyhedron* transPoly = randomTransPoly(numVars, numConstraintsPerTrans);
        lts->addTransRel((char*)transName.c_str(), (char*)preLoc.c_str(), (char*)postLoc.c_str(), transPoly);
    }

    std::cout << "|- Single cycle LTS generated." << std::endl;
}


int main() {
    ios::sync_with_stdio(false);
    srand(time(NULL));

    LinTS* root = new LinTS();
    Initialize();


    int numVars=5, numLocations=100, numTransitions=120, numConstraintsPerTrans=1, mode,test_mode;

    std::cout << "Enter number of variables: ";
    std::cin >> numVars;
    std::cout << "Enter number of locations: ";
    std::cin >> numLocations;
    std::cout << "Enter number of transitions: ";
    std::cin >> numTransitions;
    std::cout << "Enter number of constraints per transition: ";
    std::cin >> numConstraintsPerTrans;
    cout<<" Enter solving mode: 1 or 2\n";
    cin>> mode;
    cout<<" Enter test mode: 1 or 2\n";
    cin>> test_mode;
    if (test_mode==1)
        generateSingleCycleLTS(root, numVars, numLocations, numConstraintsPerTrans);
    else if (test_mode==2)
        generateRandomLTS(root,numVars,numLocations,numTransitions,numConstraintsPerTrans);
        
    if (mode == 1)
        root->ComputeLinTSInv();
    else
        root->ComputeOverInv();
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