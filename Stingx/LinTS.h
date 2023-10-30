#ifndef __LINTS_STING_H_
#define __LINTS_STING_H_

#include <ppl.hh>
#include <stack>
#include "Location.h"
#include "TransitionRelation.h"
#include "var-info.h"
// TODO: Add error detection: Locations or Transitions with duplicate names are
// not allowed.
class LinTS {
   public:
    LinTS();

    void ComputeLinTSInv(bool skipAlg);
    void ComputeInitInv();

    void tarjan(int start);
    bool tarjanAlg();

    void SplitLinTS();
    void ComputeInv();
    void Propagation();
    void PrintInv();

    LinTS* projectSubTS(vector<int> projectLocs);

    void addVariable(char* var);
    void addTransRel(char* transName,
                     char* preLoc,
                     char* postLoc,
                     C_Polyhedron* poly);
    void addLocInit(char* locName, C_Polyhedron* poly);
    void setLocPreInv(char* locName, C_Polyhedron* inv);

    Location* SearchLoc(string name);
    Location* SearchLoc(char* name);
    int SearchLocIndex(string name);

    int getVarNum() { return varNum; }
    int getVarIndex(char* var);
    int getVarIndex(string var);
    Location* getInitLocation();

    void PrintLinTS(int debugLevel = 0, bool skipBasic = false);

   private:
    // About Tarjan Alg.
    vector<vector<int>> edges;
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
    C_Polyhedron *trivial, *dualp;
    vector<Clump> clumps;
};

#endif