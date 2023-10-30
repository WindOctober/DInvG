#include "LinTS.h"
#include <stdio.h>
#include <string.h>
#include <stack>
#include "PolyUtils.h"
using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;

LinTS::LinTS() {
    info = new var_info();
    coefInfo = new var_info();
    lambdaInfo = new var_info();
    varNum = 0;
    locNum = 0;
    transNum = 0;
    (*locList).clear();
    (*transList).clear();
}

void LinTS::tarjan(int cur) {
    s.push(cur);
    visited[cur] = true;
    low[cur] = dfn[cur] = ++timeCnt;
    for (int i = 0; i < edges[cur].size(); i++) {
        int to = edges[cur][i];
        if (!visited[to]) {
            tarjan(to);
            low[cur] = min(low[to], low[cur]);
        } else {
            low[cur] = min(low[to], low[cur]);
        }
    }
    if (low[cur] == dfn[cur]) {
        sccCnt++;
        sccSize.push_back(0);
        while (true) {
            int id = s.top();
            s.pop();
            sccSize[sccCnt - 1]++;
            sccNo[id] = sccCnt - 1;
            if (id == cur)
                break;
        }
    }
    return;
}
bool LinTS::tarjanAlg() {
    // Here, I will employ the Tarjan algorithm to ascertain the distribution of
    // strongly connected components in the current transition system. Only when
    // there are no strongly connected components left in the system (i.e., it's
    // a directed acyclic graph), will the recursion not be required.

    edges.resize(locNum);
    sccNo.resize(locNum);
    for (int i = 0; i < locNum; i++) {
        visited.push_back(false);
        low.push_back(0);
        dfn.push_back(0);
    }
    for (int i = 0; i < transNum; i++) {
        TransitionRelation* trans = (*transList)[i];
        int preid = SearchLocIndex(trans->getPreLocName());
        int postid = SearchLocIndex(trans->getPostLocName());
        edges[preid].push_back(postid);
    }
    sccCnt = 0;
    timeCnt = 0;
    tarjan(initLocIndex);
    if (sccSize[initLocIndex] == locNum)
        return false;
    else
        return true;
}

void LinTS::ComputeLinTSInv(bool skipAlg) {
    for (int i = 0; i < locNum; i++) {
        if ((*locList)[i]->getInitFlag()) {
            if (initLocIndex != -1) {
                perror("[ERROR] Only one initial Location is allowed.");
            }
            initLocIndex = i;
            initLoc = (*locList)[i];
        }
    }
    bool splitFlag;
    if (!skipAlg)
        splitFlag = tarjanAlg();
    else
        splitFlag = false;
    if (splitFlag) {
        vector<int> projectSet;
        for (int i = 0; i < locNum; i++) {
            if (sccNo[i] == sccNo[initLocIndex])
                projectSet.push_back(i);
        }
        LinTS* subRoot = projectSubTS(projectSet);
    }
}

void LinTS::ComputeInitInv() {
    int coefNum = coefInfo->getDim();
    C_Polyhedron initPoly(coefNum, UNIVERSE);
    trivial = new C_Polyhedron(coefNum, UNIVERSE);
    for (int i = 0; i < locNum; i++) {
        (*locList)[i]->addTrivial(trivial);
    }
    for (int i = 0; i < locNum; i++) {
        (*locList)[i]->makeContext();
    }
    initLoc->ComputeCoefConstraints(initPoly);
    for (int i = 0; i < transNum; i++) {
        (*transList[i])->ComputeIntraConsecConstraints(clumps);
    }
    for (int i = 0; i < locNum; i++) {
        (*locList)[i]->addClump(clumps);
    }
    vector<vector<vector<int>>> actualSeqs;
    actualSeqs = GenerateSequences(initLocIndex, clumps, initPoly);
    TraverseSequences(actualSeqs, initLocIndex, clumps, initPoly);
}

LinTS* LinTS::projectSubTS(vector<int> projectLocs) {
    LinTS* subRoot = new LinTS();
    for (int i = 0; i < varNum; i++) {
        subRoot->addVariable(info->getName(i));
    }
    for (int i = 0; i < projectLocs.size(); i++) {
        int id = projectLocs[i];
        Location* loc = (*locList)[id];
        C_Polyhedron* poly = new C_Polyhedron(varNum, UNIVERSE);
        if (loc->getInitFlag()) {
            poly->intersection_assign(loc->getPolyRef());
            subRoot->addLocInit((char*)loc->getName().c_str(), poly);
        } else {
            subRoot->addLocInit((char*)loc->getName().c_str(), NULL);
        }
    }
    for (int i = 0; i < transNum; i++) {
        TransitionRelation* trans = (*transList)[i];
        int preLocIndex = SearchLocIndex(trans->getPreLocName());
        int postLocIndex = SearchLocIndex(trans->getPostLocName());
        if (sccNo[preLocIndex] != sccNo[projectLocs[0]] ||
            sccNo[postLocIndex] != sccNo[projectLocs[0]])
            continue;
        C_Polyhedron* poly = new C_Polyhedron(varNum * 2, UNIVERSE);
        poly->intersection_assign(trans->getTransRel());
        subRoot->addTransRel(trans->getName(), trans->getPreLocName(),
                             trans->getPostLocName(), poly);
    }
}

void LinTS::addVariable(char* var) {
    info->insert(var);
    varNum++;
    return;
}

void LinTS::addTransRel(char* transName,
                        char* preLoc,
                        char* postLoc,
                        C_Polyhedron* poly) {
    TransitionRelation* trans =
        new TransitionRelation(varNum, info, coefInfo, lambdaInfo, transName);
    trans->setRel(poly);
    if (!postLoc)
        postLoc = strdup(preLoc);
    trans->setLocs(SearchLoc(preLoc), SearchLoc(postLoc));
    transNum++;
    transList->push_back(trans);
    return;
}

void LinTS::addLocInit(char* locName, C_Polyhedron* poly) {
    Location* loc = new Location(varNum, info, coefInfo, lambdaInfo, locName);
    if (poly)
        loc->setPoly(poly);
    locNum++;
    locList->push_back(loc);
    return;
}
void LinTS::setLocPreInv(char* locName, C_Polyhedron* inv) {
    Location* loc = SearchLoc(locName);
    loc->setPreInvPoly(inv);
    return;
}

Location* LinTS::SearchLoc(string name) {
    for (int i = 0; i < locList->size(); i++) {
        string res = (*locList)[i]->getName();
        if (res == name)
            return (*locList)[i];
    }
    return NULL;
}
Location* LinTS::SearchLoc(char* name) {
    for (int i = 0; i < locList->size(); i++) {
        string res = (*locList)[i]->getName();
        if (res == string(name))
            return (*locList)[i];
    }
    return NULL;
}
int LinTS::SearchLocIndex(string name) {
    for (int i = 0; i < locList->size(); i++) {
        string res = (*locList)[i]->getName();
        if (res == name)
            return i;
    }
    return -1;
}

// NOTE: Get Function Part:
int LinTS::getVarIndex(char* var) {
    return info->search(var);
}
int LinTS::getVarIndex(string var) {
    return info->search(var.c_str());
}
Location* LinTS::getInitLocation() {
    for (int i = 0; i < locNum; i++) {
        bool flag = (*locList)[i]->getInitFlag();
        if (flag)
            return (*locList)[i];
    }
    prettyPrintInfo("");
    perror("[ERROR] This linear transition system lacks an initial Location.");
    return NULL;
}

void prettyPrintInfo(string str) {
    const int totalLength = 80;
    int len = str.size();
    int padLength;
    if (len > totalLength)
        padLength = 0;
    else
        padLength = (totalLength - len) / 2;

    for (int i = 0; i < padLength; ++i) {
        printf("=");
    }
    printf("%s", str.c_str());
    for (int i = 0; i < padLength; ++i) {
        printf("=");
    }
    if ((len % 2) != (totalLength % 2)) {
        printf("=");
    }

    printf("\n");
}

void LinTS::PrintLinTS(int debugLevel, bool skipBasic) {
    if (skipBasic)
        goto level1;
    prettyPrintInfo("Level 0 DebugInfo start");
    printf(
        "This linear transfer system has %d variables, %d locations, and %d "
        "transitions.\n",
        varNum, locNum, transNum);
    prettyPrintInfo("Variable Info");
    for (int i = 0; i < varNum; i++) {
        printf("Variable No.%d is : %s \n", i + 1, info->getName(i));
    }
    prettyPrintInfo("Location Info");
    for (int i = 0; i < locNum; i++) {
        Location* loc = (*locList)[i];
        string locName = loc->getName();
        printf("Location No.%d is : %s\n", i + 1, locName.c_str());
    }
    prettyPrintInfo("Transition Info");
    for (int i = 0; i < transNum; i++) {
        TransitionRelation* trans = (*transList)[i];
        string transName = trans->getName();
        string preLocName = trans->getPreLocName();
        string postLocName = trans->getPostLocName();
        printf("Transiiton No.%d is : %s\n", i + 1, transName.c_str());
        printf("Transition from Location %s -> Location %s : %d -> %d\n",
               preLocName.c_str(), postLocName.c_str(),
               SearchLocIndex(preLocName), SearchLocIndex(postLocName));
    }
    prettyPrintInfo("Level 0 DebugInfo over");
    if (debugLevel <= 0)
        return;
level1:
    prettyPrintInfo("Level 1 DebugInfo start");
    for (int i = 0; i < locNum; i++) {
        if ((*locList)[i]->getInitFlag()) {
            printf("Init Location is : %s (No.%d)",
                   (*locList)[i]->getName().c_str(), i);
            printf("\n The initial polyhedron is :");
            outputPolyhedron((*locList)[i]->get_initial(), info);
        }
    }
    for (int i = 0; i < transNum; i++) {
        int preLocIndex = SearchLocIndex((*transList)[i]->getPreLocName());
        int postLocIndex = SearchLocIndex((*transList)[i]->getPostLocName());
        printf("The Transition Relation from Location %d to Location %d is :\n",
               preLocIndex, postLocIndex);
        outputPolyhedron((*transList)[i]->getTransRelRef(), info);
    }
    prettyPrintInfo("Level 1 DebugInfo over");
    if (debugLevel <= 1)
        return;
}