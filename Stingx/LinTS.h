#ifndef __LINTS_STING_H_
#define __LINTS_STING_H_

#include <map>
#include <ppl.hh>
#include <stack>
#include <utility>
#include "Location.h"
#include "TransitionRelation.h"
#include "var-info.h"
// TODO: Add error detection: Locations or Transitions with duplicate names are
// not allowed.
// TODO: Convert the SearchLocName function into a map stl.
class LinTS {
   public:
    enum VERIFIEDRESULT { CORRECT, UNKNOWN, WRONG };
    LinTS();
    LinTS(LinTS* ts);
    void ComputeLinTSInv();
    void ComputeInitInv();
    void ComputeOverInv();
    enum VERIFIEDRESULT CheckAssertion(vector<C_Polyhedron*> constraints,vector<C_Polyhedron*> assertions);
    enum VERIFIEDRESULT CheckAssertion();
    void TraverseSequences(vector<vector<vector<int>>> sequences,
                           C_Polyhedron* initPoly);
    void TraverseSequencesTotal(vector<vector<vector<int>>> sequences,
                           C_Polyhedron* initPoly);
    vector<vector<vector<int>>> GenerateSequences(C_Polyhedron* initPoly);
    C_Polyhedron* computeOneStepTransPoly(C_Polyhedron& init,
                                          C_Polyhedron& trans);
    C_Polyhedron* getUpDimensionPoly(C_Polyhedron* poly);
    void tarjan(int start);
    bool tarjanAlg();
    void PrintInv();

    void MergeSubMap(map<string, vector<C_Polyhedron*>> subMap);
    LinTS* projectSubTS(vector<int> projectLocs, int index, C_Polyhedron* poly);

    void addVariable(char* var);
    void addTransRel(char* transName,
                     char* preLoc,
                     char* postLoc,
                     C_Polyhedron* poly);
    void addLocInit(char* locName, C_Polyhedron* poly);
    void setLocPreInv(char* locName, C_Polyhedron* inv);
    void setLocAssert(char* locName, vector<C_Polyhedron*> polys);

    Location* SearchLoc(string name);
    Location* SearchLoc(char* name);
    int SearchLocIndex(string name);

    int getVarNum() { return varNum; }
    int getLocNum() { return locNum; }
    char* getLocName(int id) {
        return (char*)(*locList)[id]->getName().c_str();
    }
    int getLocIndex(char* name);
    int getVarIndex(char* var);
    int getVarIndex(string var);
    vector<Location*> getLocList() { return *locList; }
    map<string, vector<C_Polyhedron*>> getInvMap() { return InvMap; }
    Location* getInitLocation();

    void PrintLinTS(int debugLevel = 0, bool skipBasic = false);

   private:
    // About Tarjan Alg.
    vector<vector<int>> edges;
    map<pair<int, int>, int> transInEdge;
    vector<bool> visited;
    stack<int> s;
    vector<int> low, dfn;
    int timeCnt;
    int sccCnt;
    vector<int> sccNo, sccSize;

    var_info *info, *coefInfo, *lambdaInfo;
    int varNum, locNum, transNum;
    int initLocIndex = -1;
    Location* initLoc = NULL;
    vector<Location*>* locList;
    vector<TransitionRelation*>* transList;
    map<string, vector<C_Polyhedron*>> InvMap;
    C_Polyhedron *trivial, *dualp;
    vector<Clump> clumps;
};

#endif