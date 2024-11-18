#include "LinTS.h"
#include <stdio.h>
#include <string.h>
#include <z3++.h>
#include <stack>
#include <tuple>
#include <unordered_set>
#include "PolyUtils.h"
#include "Tree.h"
using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;
using namespace z3;
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

LinTS::LinTS(LinTS* ts) {
    info = new var_info();
    coefInfo = new var_info();
    lambdaInfo = new var_info();
    for (int i = 0; i < ts->varNum; i++) {
        info->insert(ts->info->getName(i));
    }
    varNum = ts->varNum;
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
    for (auto i = 0; i < transNum; ++i) {
        (*transList)[i]->addPreInv();
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

void LinTS::ComputeOverInv() {
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
    int coefNum = coefInfo->getDim();
    C_Polyhedron initPoly(coefNum, UNIVERSE);
    trivial = new C_Polyhedron(coefNum, UNIVERSE);
    for (int i = 0; i < locNum; i++) {
        (*locList)[i]->addTrivial(trivial);
    }
    for (int i = 0; i < locNum; i++) {
        (*locList)[i]->makeContext();
    }
    for (auto i = 0; i < transNum; ++i) {
        (*transList)[i]->addPreInv();
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
    TraverseSequencesTotal(actualSeqs, &initPoly);
    for(int i=0;i<locNum;i++){
        C_Polyhedron* inv=new C_Polyhedron((*locList)[i]->GetInv());
        string locName=(*locList)[i]->getName();
        vector<C_Polyhedron*> invs;
        invs.push_back(inv);
        InvMap.insert(make_pair(locName,invs));
    }
    return;
}

// TODO: adjust this section of the code to a suitable location.
Constraint_System NegateConstraint(Constraint_System cs, int dim) {
    Constraint_System res;
    for (Constraint constraint : cs) {
        Linear_Expression linexpr;
        for (int i = 0; i < dim; i++)
            linexpr += constraint.coefficient(Variable(i)) * Variable(i);
        linexpr += constraint.inhomogeneous_term();
        res.insert((linexpr + 1) <= 0);
        if (constraint.is_equality()) {
            res.insert((linexpr - 1) >= 0);
        }
    }
    return res;
}
void TraverseSequenceForPolys(vector<vector<Constraint>>& systems,
                              vector<int>& indices,
                              vector<C_Polyhedron*>& polys,
                              int depth,
                              int& dim) {
    if (depth == systems.size()) {
        C_Polyhedron* poly = new C_Polyhedron(dim, UNIVERSE);
        for (int i = 0; i < indices.size(); i++) {
            poly->add_constraint(systems[i][indices[i]]);
        }
        polys.push_back(poly);
        return;
    }
    for (int i = 0; i < systems[depth].size(); i++) {
        indices[depth] = i;
        TraverseSequenceForPolys(systems, indices, polys, depth + 1, dim);
    }
    return;
}
enum LinTS::VERIFIEDRESULT LinTS::CheckAssertion(
    vector<C_Polyhedron*> constraints,
    vector<C_Polyhedron*> assertions) {
    cout << "Now we should to prove that A ==> B, where A is DNF : \n";
    for (int i = 0; i < constraints.size(); i++) {
        // cout << *constraints[i] << endl;
        outputPolyhedron(constraints[i], info);
    }
    cout << "\n and B is DNF: \n ";
    for (int i = 0; i < assertions.size(); i++) {
        // cout << *assertions[i] << endl;
        outputPolyhedron(assertions[i], info);
    }
    bool flag = false;
    for (int i = 0; i < constraints.size(); i++) {
        C_Polyhedron* poly = constraints[i];
        for (int j = 0; j < assertions.size(); j++) {
            Constraint_System recCS = assertions[j]->minimized_constraints();
            C_Polyhedron* tmpPoly = new C_Polyhedron(*poly);
            tmpPoly->add_constraints(recCS);
            if (!tmpPoly->is_empty()) {
                flag = true;
                break;
            }
        }
    }
    if (!flag)
        return VERIFIEDRESULT::WRONG;
    flag = false;
    vector<C_Polyhedron*> negateAssertions;
    vector<vector<Constraint>> systems;
    for (int i = 0; i < assertions.size(); i++) {
        vector<Constraint> tmp;
        C_Polyhedron* poly = assertions[i];
        for (Constraint cs :
             NegateConstraint(poly->minimized_constraints(), varNum)) {
            tmp.push_back(cs);
        }
        systems.push_back(tmp);
    }
    vector<int> seq(systems.size(), 0);
    TraverseSequenceForPolys(systems, seq, negateAssertions, 0, varNum);
    for (int i = 0; i < constraints.size(); i++) {
        C_Polyhedron* poly = constraints[i];
        for (int j = 0; j < negateAssertions.size(); j++) {
            C_Polyhedron* tmpPoly = new C_Polyhedron(*poly);
            tmpPoly->intersection_assign(*negateAssertions[j]);
            if (!tmpPoly->is_empty()) {
                flag = true;
                break;
            }
        }
        if (flag)
            break;
    }
    if (!flag)
        return VERIFIEDRESULT::CORRECT;
    flag = false;
    for (int i = 0; i < constraints.size(); i++) {
        C_Polyhedron* poly = constraints[i];
        for (int j = 0; j < negateAssertions.size(); j++) {
            C_Polyhedron* tmpPoly = new C_Polyhedron(*poly);
            C_Polyhedron* assertionPoly = negateAssertions[j];
            Variables_Set projectSet;
            for (Constraint cs : assertionPoly->minimized_constraints()) {
                for (int i = 0; i < varNum; i++) {
                    if (cs.coefficient(Variable(i)) != 0) {
                        projectSet.insert(i);
                    }
                }
            }
            context solverContext;
            // tmpPoly->remove_space_dimensions(projectSet);
            // tmpPoly->intersection_assign(*assertionPoly);
            int dim = varNum;
            vector<expr> vars;
            for (int i = 0; i < dim; i++) {
                vars.push_back(solverContext.int_const(
                    (string("var") + to_string(i)).c_str()));
            }
            solver s(solverContext);
            for (Constraint cs : tmpPoly->minimized_constraints()) {
                expr tmpExpr = solverContext.int_val(0);
                for (int i = 0; i < dim; i++) {
                    tmpExpr =
                        tmpExpr +
                        vars[i] * solverContext.int_val(int(
                                      cs.coefficient(Variable(i)).get_si()));
                }
                tmpExpr = tmpExpr + solverContext.int_val(
                                        int(cs.inhomogeneous_term().get_si()));
                if (cs.is_equality())
                    s.add(tmpExpr == 0);
                else
                    s.add(tmpExpr >= 0);
            }
            for (Constraint cs : assertionPoly->minimized_constraints()) {
                expr tmpExpr = solverContext.int_val(0);
                for (int i = 0; i < dim; i++) {
                    tmpExpr =
                        tmpExpr +
                        vars[i] * solverContext.int_val(int(
                                      cs.coefficient(Variable(i)).get_si()));
                }
                tmpExpr = tmpExpr + solverContext.int_val(
                                        int(cs.inhomogeneous_term().get_si()));
                if (cs.is_equality())
                    s.add(tmpExpr == 0);
                else
                    s.add(tmpExpr >= 0);
            }
            if (s.check() == z3::sat) {
                cout << "sat" << endl << s.get_model() << endl;
                flag = true;
                break;
            }
        }
        if (flag)
            break;
    }
    if (!flag)
        return VERIFIEDRESULT::CORRECT;
    return VERIFIEDRESULT::UNKNOWN;
}

enum LinTS::VERIFIEDRESULT LinTS::CheckAssertion() {
    return VERIFIEDRESULT::CORRECT;
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
    // cout << endl << "/ Generate Sequences";
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
    // cout << endl << "/ Read(Traverse) Sequences";
    tr.treeSeqTraverse(sequences, *initPoly, invCoefPoly);
    return;
}

void LinTS::TraverseSequencesTotal(vector<vector<vector<int>>> sequences,
                              C_Polyhedron* initPoly) {
    C_Polyhedron invCoefPoly(*trivial);
    Tree tr = Tree();
    tr.setCurId(initLocIndex);
    tr.setInfo(info, coefInfo, lambdaInfo);
    tr.setLocTrans(locList, transList);
    tr.deactivateProject();
    for (auto it = clumps.begin(); it < clumps.end(); it++) {
        (*it).resetIter();
    }
    tr.setPriorClumps(clumps);
    tr.setMaxPolyNum();
    // cout << endl << "/ Read(Traverse) Sequences";
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

C_Polyhedron* LinTS::getUpDimensionPoly(C_Polyhedron* poly) {
    C_Polyhedron* newPoly = new C_Polyhedron(varNum * 2, UNIVERSE);

    Constraint_System cs = poly->constraints();
    Constraint_System res;

    for (const Constraint& c : cs) {
        Linear_Expression le;
        for (unsigned int i = 0; i < varNum; ++i) {
            Coefficient coef = c.coefficient(Variable(i));
            le += coef * Variable(varNum + i);
        }
        if (c.is_equality()) {
            res.insert(le + c.inhomogeneous_term() == 0);
        } else if (c.is_inequality()) {
            res.insert(le + c.inhomogeneous_term() >= 0);
        } else {
            throw runtime_error("");
        }
    }

    newPoly->add_constraints(res);

    return newPoly;
}

void LinTS::MergeSubMap(std::map<string, vector<C_Polyhedron*>> subMap) {
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
    info->searchElseInsert(var);
    varNum = info->getDim();
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
void LinTS::setLocAssert(char* locName, vector<C_Polyhedron*> polys) {
    Location* loc = SearchLoc(locName);
    loc->setAssertion(polys);
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
int LinTS::getLocIndex(char* name) {
    for (int i = 0; i < locNum; i++) {
        Location* loc = (*locList)[i];
        string locName = loc->getName();
        if (string(name) == locName)
            return i;
    }
    return -1;
}
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

bool LinTS::PrintInv() {
    bool empty=true;
    for (int i = 0; i < locNum; i++) {
        string name = (*locList)[i]->getName();
        if (InvMap.find(name) == InvMap.end()) {
            prettyPrintInfo("The invariant for Location " + name + "is empty");
            continue;
        }
        empty = false;
        vector<C_Polyhedron*> disInv = InvMap[name];
        prettyPrintInfo("The invariant for Location " + name);
        for (int i = 0; i < disInv.size(); i++) {
            outputPolyhedron(disInv[i], info);
        }
    }
    return empty;
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