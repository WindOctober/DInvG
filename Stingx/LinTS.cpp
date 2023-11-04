#include "LinTS.h"
#include <stdio.h>
#include <string.h>
#include <stack>
#include <tuple>
#include <unordered_set>
#include "PolyUtils.h"
#include "Tree.h"
using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;

void prettyPrintInfo(string str);
LinTS::LinTS() {
    info = new var_info();
    coefInfo = new var_info();
    lambdaInfo = new var_info();
    varNum = 0;
    locNum = 0;
    transNum = 0;
    initLocIndex = -1;
    initLoc = NULL;
    locList = new vector<Location*>();
    transList = new vector<TransitionRelation*>();
    return;
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
    InvMap.clear();
    for (int i = 0; i < locNum; i++) {
        string locName = string((*locList)[i]->getName());
        vector<C_Polyhedron*> empty;
        empty.clear();
        InvMap.insert(make_pair(locName, empty));
    }
    for (int i = 0; i < locNum; i++) {
        visited.push_back(false);
        low.push_back(0);
        dfn.push_back(0);
        sccNo[i] = -1;
    }
    for (int i = 0; i < transNum; i++) {
        TransitionRelation* trans = (*transList)[i];
        int preid = SearchLocIndex(trans->getPreLocName());
        int postid = SearchLocIndex(trans->getPostLocName());
        edges[preid].push_back(postid);
        transInEdge.insert(
            pair<pair<int, int>, int>(make_pair(preid, postid), i));
    }
    sccCnt = 0;
    timeCnt = 0;
    tarjan(initLocIndex);
    if (sccSize[sccNo[initLocIndex]] == locNum)
        return false;
    else
        return true;
}

void LinTS::ComputeLinTSInv() {
    for (int i = 0; i < locNum; i++) {
        if ((*locList)[i]->getInitFlag()) {
            if (initLocIndex != -1) {
                perror("[ERROR] Only one initial Location is allowed.");
            }
            initLocIndex = i;
            initLoc = (*locList)[i];
        }
    }
    if (initLocIndex == -1)
        return;
    bool splitFlag = tarjanAlg();
    // It's important to note that if splitFlag=True, it indicates that the
    // current graph contains multiple SCCs. In this case, our strategy should
    // be to compute for each SCC one by one, propagating the invariants through
    // them in the order of DFS (since the graph, after SCC contraction, is
    // definitely a Directed Acyclic Graph or DAG).
    if (splitFlag) {
        stack<tuple<int, int, C_Polyhedron*>> s;
        s.push(make_tuple(sccNo[initLocIndex], initLocIndex,
                          initLoc->get_initial()));
        while (!s.empty()) {
            int curScc = get<0>(s.top());
            int initId = get<1>(s.top());
            C_Polyhedron* initPoly = get<2>(s.top());
            s.pop();
            vector<int> projectSet;
            for (int i = 0; i < locNum; i++) {
                if (sccNo[i] == curScc)
                    projectSet.push_back(i);
            }
            LinTS* subRoot = projectSubTS(projectSet, initId, initPoly);
            subRoot->ComputeLinTSInv();
            MergeSubMap(subRoot->getInvMap());
            for (int i = 0; i < transNum; i++) {
                TransitionRelation* trans = (*transList)[i];
                int preId = SearchLocIndex(trans->getPreLocName());
                int postId = SearchLocIndex(trans->getPostLocName());
                if (sccNo[preId] != curScc || sccNo[postId] == curScc)
                    continue;
                for (int polyId = 0;
                     polyId < InvMap[trans->getPreLocName()].size(); polyId++) {
                    C_Polyhedron* prePoly =
                        InvMap[trans->getPreLocName()][polyId];
                    C_Polyhedron transPoly = trans->getTransRel();
                    C_Polyhedron* resPoly =
                        computeOneStepTransPoly(*prePoly, transPoly);
                    s.push(make_tuple(sccNo[postId], postId, resPoly));
                }
            }
        }
        return;
    }
    // The LinTS that arrives here should be a complete SCC, indivisible.
    ComputeInitInv();
    InvMap[initLoc->getName()].push_back(&(initLoc->getInvRef()));
    // Now that we know the invariant of the initial node of this SCC, we can
    // remove this node from the SCC and analyze the invariant of the resulting
    // graph.
    vector<int> projectset;
    LinTS* subRoot;
    for (int i = 0; i < locNum; i++) {
        if (i != initLocIndex)
            projectset.push_back(i);
    }
    if (projectset.size() == 0)
        return;
    for (int i = 0; i < edges[initLocIndex].size(); i++) {
        int to = edges[initLocIndex][i];
        if (to == initLocIndex)
            continue;
        pair<int, int> key = make_pair(initLocIndex, to);
        if (transInEdge.find(key) == transInEdge.end()) {
            perror("[ERROR] The expected edge cannot be found.");
        }
        TransitionRelation* trans = (*transList)[transInEdge[key]];
        C_Polyhedron initPoly = initLoc->GetInv();
        C_Polyhedron transPoly = trans->getTransRel();
        C_Polyhedron* newInitPoly =
            computeOneStepTransPoly(initPoly, transPoly);
        subRoot = projectSubTS(projectset, to, newInitPoly);
        subRoot->ComputeLinTSInv();
        MergeSubMap(subRoot->getInvMap());
        delete subRoot;
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
        (*transList)[i]->ComputeIntraConsecConstraints(clumps);
    }
    for (int i = 0; i < locNum; i++) {
        (*locList)[i]->addClump(clumps);
    }
    vector<vector<vector<int>>> actualSeqs;
    actualSeqs = GenerateSequences(&initPoly);
    TraverseSequences(actualSeqs, &initPoly);
    return;
}

vector<vector<vector<int>>> LinTS::GenerateSequences(C_Polyhedron* initPoly) {
    Tree tr = Tree();
    tr.setCurId(initLocIndex);
    tr.setInfo(info, coefInfo, lambdaInfo);
    tr.setLocTrans(locList, transList);
    for (auto it = clumps.begin(); it < clumps.end(); it++) {
        (*it).resetIter();
    }
    tr.setPriorClumps(clumps);
    tr.setMaxPolyNum();
    cout << endl << "/ Generate Sequences";
    vector<vector<vector<int>>> sequences;
    sequences = tr.seqGen("two_per_group", *initPoly);
    return sequences;
}

void LinTS::TraverseSequences(vector<vector<vector<int>>> sequences,
                              C_Polyhedron* initPoly) {
    C_Polyhedron invCoefPoly(*trivial);
    Tree tr = Tree();
    tr.setCurId(initLocIndex);
    tr.setInfo(info, coefInfo, lambdaInfo);
    tr.setLocTrans(locList, transList);
    for (auto it = clumps.begin(); it < clumps.end(); it++) {
        (*it).resetIter();
    }
    tr.setPriorClumps(clumps);
    tr.setMaxPolyNum();
    cout << endl << "/ Read(Traverse) Sequences";
    tr.treeSeqTraverse(sequences, *initPoly, invCoefPoly);
    return;
}

C_Polyhedron* LinTS::computeOneStepTransPoly(C_Polyhedron& init,
                                             C_Polyhedron& trans) {
    Variables_Set projectSet;
    for (int i = 0; i < varNum; i++) {
        projectSet.insert(Variable(i));
    }
    C_Polyhedron* newInitPoly = new C_Polyhedron(varNum * 2, UNIVERSE);
    for (auto constraint : init.minimized_constraints()) {
        newInitPoly->add_constraint(constraint);
    }
    for (auto constraint : trans.minimized_constraints()) {
        newInitPoly->add_constraint(constraint);
    }
    newInitPoly->remove_space_dimensions(projectSet);
    return newInitPoly;
}

void LinTS::MergeSubMap(map<string, vector<C_Polyhedron*>> subMap) {
    for (auto it = subMap.begin(); it != subMap.end(); it++) {
        string LocName = (*it).first;
        vector<C_Polyhedron*> disInv = (*it).second;
        if (InvMap.find(LocName) == InvMap.end()) {
            perror("[ERROR] The expected Location cannot be found.");
        }
        disInv.insert(disInv.end(), InvMap[LocName].begin(),
                      InvMap[LocName].end());
        InvMap[LocName] = disInv;
    }
    return;
}
LinTS* LinTS::projectSubTS(vector<int> projectLocs,
                           int initIndex,
                           C_Polyhedron* initPoly) {
    LinTS* subRoot = new LinTS();
    unordered_set<int> projectSet;
    for (int i = 0; i < varNum; i++) {
        subRoot->addVariable(info->getName(i));
    }
    for (int i = 0; i < projectLocs.size(); i++) {
        int id = projectLocs[i];
        projectSet.insert(id);
        Location* loc = (*locList)[id];
        C_Polyhedron* poly = new C_Polyhedron(varNum, UNIVERSE);
        if (id == initIndex) {
            poly->intersection_assign(*initPoly);
            subRoot->addLocInit((char*)loc->getName().c_str(), poly);
        } else {
            subRoot->addLocInit((char*)loc->getName().c_str(), NULL);
        }
    }
    for (int i = 0; i < transNum; i++) {
        TransitionRelation* trans = (*transList)[i];
        int preLocIndex = SearchLocIndex(trans->getPreLocName());
        int postLocIndex = SearchLocIndex(trans->getPostLocName());
        if (projectSet.find(preLocIndex) == projectSet.end() ||
            projectSet.find(postLocIndex) == projectSet.end())
            continue;
        C_Polyhedron* poly = new C_Polyhedron(varNum * 2, UNIVERSE);
        poly->intersection_assign(trans->getTransRel());
        subRoot->addTransRel((char*)trans->getName().c_str(),
                             (char*)trans->getPreLocName().c_str(),
                             (char*)trans->getPostLocName().c_str(), poly);
    }
    return subRoot;
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
    if (poly->is_empty())
        return;
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
    if (poly && !poly->is_empty())
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

void LinTS::PrintInv() {
    for (int i = 0; i < locNum; i++) {
        string name = (*locList)[i]->getName();
        if (InvMap.find(name) == InvMap.end()) {
            prettyPrintInfo("The invariant for Location " + name + "is empty");
            continue;
        }
        vector<C_Polyhedron*> disInv = InvMap[name];
        prettyPrintInfo("The invariant for Location " + name);
        for (int i = 0; i < disInv.size(); i++) {
            outputPolyhedron(disInv[i], info);
        }
    }
    return;
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