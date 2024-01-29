#include "CParser.h"
#include <stdexcept>
#include <utility>
#include "ParserUtility.h"
#include "ProgramState.h"
using namespace std;
using namespace llvm;
using namespace clang;

// NOTE : In this version of the code, we require all variables to be declared
// in advance, avoiding separate declarations of local variables within branch
// statements. The handling of local variables and projection optimization will
// be further refined in the future.

extern ASTContext* globalContext;

CParser::CParser(ASTContext* context, ParserState state) {
    if (pselect == nullptr)
        pState = state;
    globalContext = context;
    LoopCount = 0;
    globalLocCount = 0;
    return;
}

void PrintIndent(int indent) {
    for (int i = 0; i < indent; i++)
        outs() << "\t";
    return;
}

void PrintStmtInfo(Stmt* stmt, int indent) {
    if (!stmt)
        return;
    outs() << "\n";
    PrintIndent(indent);
    outs() << stmt->getStmtClassName() << "\n";
    if (isa<IfStmt>(stmt)) {
        IfStmt* ifstmt = dyn_cast<IfStmt>(stmt);
        PrintIndent(indent);
        outs() << "IfStmt Cond: ";
        PrintExpr(ifstmt->getCond());
        outs() << "\n";
        PrintIndent(indent);
        outs() << "IfStmt ThenBranch:";
        PrintStmtInfo(ifstmt->getThen(), indent + 1);
        if (ifstmt->hasElseStorage()) {
            outs() << "\n";
            PrintIndent(indent);
            outs() << "IfStmt ElseBranch:";
            PrintStmtInfo(ifstmt->getElse(), indent + 1);
        }
    } else if (isa<WhileStmt>(stmt)) {
        WhileStmt* whilestmt = dyn_cast<WhileStmt>(stmt);
        PrintIndent(indent);
        outs() << "WhileStmt Cond: ";
        PrintExpr(whilestmt->getCond());
        outs() << "\n";
        PrintIndent(indent);
        outs() << "WhileStmt body: ";
        PrintStmtInfo(whilestmt->getBody(), indent + 1);
    } else if (isa<DoStmt>(stmt)) {
        DoStmt* dostmt = dyn_cast<DoStmt>(stmt);
        PrintIndent(indent);
        outs() << "DoStmt Cond: ";
        PrintExpr(dostmt->getCond());
        outs() << "\n";
        PrintIndent(indent);
        outs() << "DoStmt body: ";
        PrintStmtInfo(dostmt->getBody(), indent + 1);
    } else if (isa<ForStmt>(stmt)) {
        ForStmt* forstmt = dyn_cast<ForStmt>(stmt);
        PrintIndent(indent);
        outs() << "ForStmt Cond: ";
        PrintExpr(forstmt->getCond());
        outs() << "\n";
        PrintIndent(indent);
        outs() << "ForStmt Init: ";
        PrintStmtInfo(forstmt->getInit(), indent);
        outs() << "\n";
        PrintIndent(indent);
        outs() << "ForStmt Inc: ";
        PrintExpr(forstmt->getInc());
        outs() << "\n";
        PrintIndent(indent);
        outs() << "ForStmt body: ";
        PrintStmtInfo(forstmt->getBody(), indent + 1);
    } else if (isa<ContinueStmt>(stmt)) {
    } else if (isa<BreakStmt>(stmt)) {
    } else if (isa<ReturnStmt>(stmt)) {
    } else if (isa<CompoundStmt>(stmt)) {
        CompoundStmt* compound = dyn_cast<CompoundStmt>(stmt);
        for (Stmt* stmt : compound->body()) {
            PrintStmtInfo(stmt, indent + 1);
        }
    } else if (isa<DeclStmt>(stmt)) {
        DeclStmt* decls = dyn_cast<DeclStmt>(stmt);
        for (Decl* singledecl : decls->getDeclGroup()) {
            if (isa<VarDecl>(singledecl)) {
                VarDecl* vardecl = dyn_cast<VarDecl>(singledecl);
                PrintIndent(indent);
                outs() << "VarDecl is : " << vardecl->getNameAsString();
                outs() << "\n";
                PrintIndent(indent);
                outs() << vardecl->getNameAsString() << "'s InitVal is : ";
                PrintExpr(vardecl->getInit());
                outs() << "\n";
            }
        }
    } else if (isa<BinaryOperator>(stmt)) {
        BinaryOperator* binary = dyn_cast<BinaryOperator>(stmt);
        PrintIndent(indent);
        outs() << "Binary Opcode is : " << binary->getOpcodeStr();
        outs() << "\n";
        PrintIndent(indent);
        outs() << "Left Expr is : ";
        PrintExpr(binary->getLHS());
        outs() << "\n";
        PrintIndent(indent);
        outs() << "Right Expr is : ";
        PrintExpr(binary->getRHS());
        outs() << "\n";
    } else if (isa<CallExpr>(stmt)) {
        CallExpr* callexpr = dyn_cast<CallExpr>(stmt);
        if (callexpr->getDirectCallee()) {
            PrintIndent(indent);
            outs() << "CallExpr Function: "
                   << callexpr->getDirectCallee()->getNameAsString();
            outs() << "\n";
            PrintIndent(indent);
            outs() << "CallExpr Arguments: ";
            for (int i = 0, j = callexpr->getNumArgs(); i < j; i++) {
                if (i > 0)
                    outs() << ", ";
                PrintExpr(callexpr->getArg(i));
            }
            outs() << "\n";
        }
    } else if (isa<UnaryOperator>(stmt)) {
        UnaryOperator* unop = dyn_cast<UnaryOperator>(stmt);
        PrintIndent(indent);
        outs() << "UnaryOperator Opcode: "
               << UnaryOperator::getOpcodeStr(unop->getOpcode());
        outs() << "\n";
        PrintIndent(indent);
        outs() << "UnaryOperator SubExpr: ";
        PrintExpr(unop->getSubExpr());
        outs() << "\n";
    } else {
        throw runtime_error(
            "An unauthorized Stmt type was encountered when outputting "
            "StmtInfo.");
    }
}

// The parser begins with the entry into the VisitFunctionDecl function, which
// then confirms the main function. Within the main function, it analyzes the
// required System and invokes backend tools for solving.
bool CParser::VisitFunctionDecl(FunctionDecl* funcDecl) {
    // if (pState == ParserState::PREPROCESS) {
    //     return true;
    // }
    if (!funcDecl->hasBody())
        return true;
    SourceManager& manager = globalContext->getSourceManager();
    if (!manager.isInMainFile(funcDecl->getLocation()))
        return true;
    string funcName = funcDecl->getNameAsString();
    if (funcName != "main")
        return true;
    Stmt* funcBody = funcDecl->getBody();
    if (!isa<CompoundStmt>(funcBody)) {
        throw runtime_error(
            "The body of the function is not a compound statement?");
    }
    ProgramState* proState = new ProgramState();
    // PrintStmtInfo(funcBody, 0);
    // exit(0);
    finalRes = LinTS::VERIFIEDRESULT::CORRECT;
    proState->setLocIndex(globalLocCount);
    TraverseProgramStmt(funcBody, proState, NULL, true);
    cout << "\n\n**THE FINAL RESULT IS**\n\n";
    string strRes;
    if (finalRes == LinTS::VERIFIEDRESULT::CORRECT)
        strRes = "CORRECT";
    else if (finalRes == LinTS::VERIFIEDRESULT::WRONG)
        strRes = "WRONG";
    else
        strRes = "UNKNOWN";
    cout << "*********************" << strRes
         << "******************************";
    return false;
}

// This function deals with the impact of each specific statement on the current
// program state, as well as the potential influence on the overall LinTS.

// NOTE: We mainly handle the following statements: IfStmt, WhileStmt, DoStmt,
// ForStmt, ContinueStmt, BreakStmt, ReturnStmt, CompoundStmt, DeclStmt,
// BinaryOperator, CallExpr.
void CParser::ComputeLinTSInv(int index, ProgramState* curState) {
    LinTS* baseTS = linTSMap[index];
    vector<C_Polyhedron*> exitInv;
    vector<C_Polyhedron*>& initPolys = linTSInit[index];
    vector<char*> locNameList;
    vector<Location*> loclist = baseTS->getLocList();
    map<int, int> tmpIdMap = LocIdMap[index];
    unordered_set<int> breakHash = LinTSBreakLoc[index];
    for (int i = 0; i < loclist.size(); i++)
        locNameList.push_back((char*)loclist[i]->getName().c_str());
    vector<vector<C_Polyhedron*>> transPolys;
    vector<C_Polyhedron*> upLocConstraintsPolys;
    for (int i = 0; i < loclist.size(); i++) {
        vector<C_Polyhedron*>& recPolys =
            linTSLocConstrants[index][tmpIdMap[i]];

        assert(recPolys.size() <= 1);
        if (recPolys.size() == 0)
            recPolys.push_back(new C_Polyhedron(baseTS->getVarNum(), UNIVERSE));
        upLocConstraintsPolys.push_back(
            baseTS->getUpDimensionPoly(recPolys[0]));
    }

    for (int i = 0; i < loclist.size(); i++) {
        int leftId = tmpIdMap[i];
        vector<C_Polyhedron*> resTransPolysOuter;
        if (breakHash.find(leftId) != breakHash.end()) {
            transPolys.push_back(resTransPolysOuter);
            continue;
        }
        for (int j = 0; j < loclist.size(); j++) {
            int rightId = tmpIdMap[j];
            C_Polyhedron* leftConstraints = nullptr;
            C_Polyhedron* rightConstraints =
                linTSLocConstrants[index][rightId][0];
            if (!linTSLocNondetFlags[index][leftId][0]) {
                leftConstraints = linTSLocConstrants[index][leftId][0];
            }
            C_Polyhedron* leftVarEqualities = linTSLocEqualities[index][leftId];

            Constraint_System cs;
            for (auto tmp : leftVarEqualities->minimized_constraints())
                cs.insert(tmp);
            if (leftConstraints)
                for (auto tmp : leftConstraints->minimized_constraints())
                    cs.insert(tmp);
            for (auto tmp : upLocConstraintsPolys[j]->minimized_constraints())
                cs.insert(tmp);
            C_Polyhedron* poly = new C_Polyhedron(cs);
            // cout << *leftVarEqualities << endl;
            // cout << *upLocConstraintsPolys[j] << endl;
            // cout << *leftConstraints << endl;
            // cout << *poly << endl;
            // cout<<endl;
            if (poly->is_empty())
                resTransPolysOuter.push_back(NULL);
            else
                resTransPolysOuter.push_back(poly);
        }
        transPolys.push_back(resTransPolysOuter);
    }
    for (int i = 0; i < initPolys.size(); i++) {
        for (int j = 0; j < loclist.size(); j++) {
            C_Polyhedron* legalTest = new C_Polyhedron(*initPolys[i]);
            legalTest->intersection_assign(
                *linTSLocConstrants[index][tmpIdMap[j]][0]);
            if (legalTest->is_empty()) {
                continue;
            }
            vector<C_Polyhedron*> PreInv(
                loclist.size(),
                new C_Polyhedron(baseTS->getVarNum(), UNIVERSE));
            int strengthenTime = 1;
            while (true) {
                LinTS* curTS = new LinTS(baseTS);
                for (int id = 0; id < loclist.size(); id++) {
                    if (id != j) {
                        curTS->addLocInit(locNameList[id], NULL);
                    } else {
                        curTS->addLocInit(locNameList[id], initPolys[i]);
                    }
                    curTS->setLocPreInv(locNameList[id], PreInv[id]);
                }
                for (int start = 0; start < loclist.size(); start++) {
                    int leftId = tmpIdMap[start];
                    if (breakHash.find(leftId) != breakHash.end()) {
                        continue;
                    }
                    for (int end = 0; end < loclist.size(); end++) {
                        int rightId = tmpIdMap[end];
                        string str = "Trans_From_" + to_string(start) + "_to_" +
                                     to_string(end);
                        char *preName = locNameList[start],
                             *postName = locNameList[end],
                             *transName = (char*)str.c_str();
                        if (transPolys[start][end])
                            curTS->addTransRel(transName, preName, postName,
                                               transPolys[start][end]);
                    }
                }
                curTS->PrintLinTS(1);
                curTS->ComputeLinTSInv();
                map<string, vector<C_Polyhedron*>> invMap = curTS->getInvMap();
                curTS->PrintInv();
                // TODO: consider more complicated case.
                bool restartFlag = false;
                for (int k = 0; k < loclist.size(); k++) {
                    vector<C_Polyhedron*> invPolys =
                        invMap[loclist[k]->getName()];
                    if (invPolys.size() == 1) {
                        C_Polyhedron* tmpPoly = invPolys[0];
                        if (!tmpPoly->contains(*PreInv[k])) {
                            restartFlag = true;
                            PreInv[k] = tmpPoly;
                        }
                    }
                }
                if (restartFlag && strengthenTime) {
                    strengthenTime--;
                    continue;
                }
                enum LinTS::VERIFIEDRESULT result=LinTS::VERIFIEDRESULT::CORRECT;
                for (int k = 0; k < loclist.size(); k++) {
                    vector<C_Polyhedron*> assertions =
                        linTSAssertion[index][tmpIdMap[k]];
                    if (assertions.size() != 0 && invMap[loclist[k]->getName()].size()!=0) {
                        result = curTS->CheckAssertion(
                            invMap[loclist[k]->getName()], assertions);
                    }
                    if (result == LinTS::VERIFIEDRESULT::UNKNOWN) {
                        if (finalRes != LinTS::VERIFIEDRESULT::WRONG)
                            finalRes = LinTS::VERIFIEDRESULT::UNKNOWN;
                    } else if (result == LinTS::VERIFIEDRESULT::WRONG) {
                        finalRes = LinTS::VERIFIEDRESULT::WRONG;
                    }
                }

                vector<C_Polyhedron*> exitConds = loopExitCond[index];
                vector<bool> flags = loopExitFlags[index];
                Variables_Set projectSet;
                for (int k = 0; k < curTS->getVarNum(); k++)
                    projectSet.insert(Variable(k));
                for (int k = 0; k < loclist.size(); k++) {
                    int recId = tmpIdMap[k];
                    vector<C_Polyhedron*> inv = invMap[loclist[k]->getName()];
                    C_Polyhedron* locConstraints =
                        linTSLocConstrants[index][recId][0];
                    C_Polyhedron* trans = linTSLocEqualities[index][recId];
                    for (int invId = 0; invId < inv.size(); invId++) {
                        for (int id = 0; id < exitConds.size(); id++) {
                            C_Polyhedron* cond = exitConds[id];
                            cond = curTS->getUpDimensionPoly(cond);

                            C_Polyhedron* res = new C_Polyhedron(
                                2 * curTS->getVarNum(), UNIVERSE);
                            res->add_constraints(
                                inv[invId]->minimized_constraints());
                            res->add_constraints(
                                trans->minimized_constraints());
                            if (breakHash.find(recId) == breakHash.end())
                                res->add_constraints(
                                    cond->minimized_constraints());
                            res->add_constraints(
                                locConstraints->minimized_constraints());
                            res->remove_space_dimensions(projectSet);
                            cout << endl << "[Exit Invariant]: ";
                            cout << *res << endl;

                            exitInv.push_back(res);

                            if (flags[id] && !cond->is_universe()) {
                                C_Polyhedron* res = new C_Polyhedron(
                                    2 * curTS->getVarNum(), UNIVERSE);
                                res->add_constraints(
                                    inv[invId]->minimized_constraints());
                                res->add_constraints(
                                    trans->minimized_constraints());
                                res->add_constraints(
                                    locConstraints->minimized_constraints());
                                res->remove_space_dimensions(projectSet);
                                cout << endl << "[Exit Invariant]: ";
                                cout << *res << endl;
                                exitInv.push_back(res);
                            }
                        }
                    }
                }
                break;
            }
        }
    }
    curState->clearVarState();
    curState->clearConstraints();
    curState->addConstraint(exitInv);
}

Expr* CParser::ProcessSpecialFunction(string funcName,
                                      CallExpr* call,
                                      ProgramState* state) {
    if (funcName == "__VERIFIER_assert") {
        // NOTE : Assertions must not contain statements related to
        // nondeterminism, as they are meaningless in this context
        Expr* assertion = call->getArg(0);
        if (!state->IsInLoop()) {
            LinTS* curTS = linTSMap[state->getLoopIndex()];
            if (!curTS)
                curTS = new LinTS();
            for (string name : state->getVarList()) {
                curTS->addVariable((char*)name.c_str());
            }
            enum LinTS::VERIFIEDRESULT result = curTS->CheckAssertion(
                state->getConstraints().first,
                state->TransformExprIntoDisjunctiveForm(assertion, true).first);
            if (result == LinTS::VERIFIEDRESULT::UNKNOWN) {
                if (finalRes != LinTS::VERIFIEDRESULT::WRONG)
                    finalRes = LinTS::VERIFIEDRESULT::UNKNOWN;
            } else if (result == LinTS::VERIFIEDRESULT::WRONG) {
                finalRes = LinTS::VERIFIEDRESULT::WRONG;
            }
            return NULL;
        }
        if (call->getNumArgs() > 1) {
            throw runtime_error(
                "The __VERIFIER_assert function has parameters other than the "
                "assertion, please confirm the relevant specifications.");
        }
        state->addAssertion(
            state->TransformExprIntoDisjunctiveForm(assertion, true).first);
        return NULL;
    } else if (funcName == "assert") {
        throw runtime_error(
            "Please complete the settings related to the assert function.");
    } else if (funcName.find("__VERIFIER_nondet_") != funcName.npos) {
        return call;
    } else if (funcName == "abort") {
        state->setEnd();
        return NULL;
    } else if (funcName == "reach_error") {
        finalRes = LinTS::VERIFIEDRESULT::WRONG;
        state->setEnd();
        return NULL;
    } else if (funcName == "assume_abort_if_not") {
        Expr* assertion = call->getArg(0);
        state->addConstraint(assertion);
        return NULL;
    }
    return NULL;
}
Expr* CParser::PreProcessExpr(Expr* expr, ProgramState* state) {
    if (isa<UnaryOperator>(expr)) {
        UnaryOperator* unary = dyn_cast<UnaryOperator>(expr);
        UnaryOperatorKind opcode = unary->getOpcode();
        if (opcode == UO_PreDec || opcode == UO_PostDec ||
            opcode == UO_PreInc || opcode == UO_PostInc) {
            Expr* subExpr = unary->IgnoreParenCasts();
            unary = dyn_cast<UnaryOperator>(subExpr);
            subExpr = unary->getSubExpr();
            if (isa<DeclRefExpr>(subExpr)) {
                DeclRefExpr* ref = dyn_cast<DeclRefExpr>(subExpr);
                string varName = ref->getDecl()->getNameAsString();
                VarDecl* var = CreateVarDecl(varName, ref->getType());
                ref = CreateVarRefExpr(var);
                BinaryOperatorKind assignKind, returnKind;
                if (opcode == UO_PreDec || opcode == UO_PostDec) {
                    assignKind = BO_Sub;
                    returnKind = BO_Add;
                } else {
                    assignKind = BO_Add;
                    returnKind = BO_Sub;
                }
                state->ProcessAssign(CreateBinaryOperator(
                    ref,
                    CreateBinaryOperator(ref, createIntegerLiteral(1),
                                         assignKind, ref->getType()),
                    BO_Assign, ref->getType()));
                if (opcode == UO_PreDec || opcode == UO_PreInc)
                    return ref;
                else
                    return CreateBinaryOperator(ref, createIntegerLiteral(1),
                                                returnKind, ref->getType());
            } else {
                throw runtime_error(
                    "In unary operators, the sub-elements are not the most "
                    "basic variable references (temporarily does not support "
                    "pointers, etc.).");
            }
        }
    } else if (isa<BinaryOperator>(expr)) {
        BinaryOperator* binary = dyn_cast<BinaryOperator>(expr);
        BinaryOperatorKind kind = binary->getOpcode();

        if (kind == BO_SubAssign || kind == BO_AddAssign ||
            kind == BO_MulAssign) {
            BinaryOperatorKind resKind;
            if (kind == BO_SubAssign)
                resKind = BO_Sub;
            else if (kind == BO_AddAssign)
                resKind = BO_Add;
            else if (kind == BO_MulAssign)
                resKind = BO_Mul;
            QualType resType = binary->getLHS()->getType();
            binary = CreateBinaryOperator(
                binary->getLHS(),
                CreateBinaryOperator(binary->getLHS(), binary->getRHS(),
                                     resKind, resType),
                BO_Assign, resType);
            kind = BO_Assign;
        }
        Expr* left = PreProcessExpr(binary->getLHS(), state);
        Expr* right = PreProcessExpr(binary->getRHS(), state);
        if (kind != BO_Assign) {
            if (isa<CallExpr>(left))
                return left;
            else if (isa<CallExpr>(right))
                return right;
            else
                return CreateBinaryOperator(left, right, kind,
                                            binary->getType());
        } else {
            state->ProcessAssign(
                CreateBinaryOperator(left, right, kind, binary->getType()));
            return binary->getLHS();
        }

    } else if (isa<CallExpr>(expr)) {
        CallExpr* call = dyn_cast<CallExpr>(expr);
        FunctionDecl* funcDecl = call->getDirectCallee();
        if (!funcDecl)
            return NULL;
        string funcName = funcDecl->getNameAsString();
        return ProcessSpecialFunction(funcName, call, state);
    } else if (isa<ImplicitCastExpr>(expr)) {
        ImplicitCastExpr* implicit = dyn_cast<ImplicitCastExpr>(expr);
        return PreProcessExpr(implicit->getSubExpr(), state);
    }
    return expr;
}

void CParser::ProcessProgramState(ProgramState* state) {
    if (!state->IsInLoop())
        return;
    int curIndex = state->getLoopIndex();
    if (linTSMap.find(curIndex) == linTSMap.end()) {
        throw runtime_error(
            "The currently accessed LinTS has not yet been created.");
    }
    LinTS* curLinTS = linTSMap[curIndex];
    char* curLocName = (char*)state->getLocName().c_str();
    int locIndex = state->getLocIndex();
    vector<string> varList = state->getVarList();
    curLinTS->addLocInit(curLocName, NULL);
    // cout << curLocName << " " << locIndex << endl;
    for (int i = 0; i < varList.size(); i++) {
        curLinTS->addVariable((char*)varList[i].c_str());
    }
    if (state->getBreakFlag()) {
        if (LinTSBreakLoc.find(curIndex) == LinTSBreakLoc.end()) {
            unordered_set<int> resHash;
            resHash.insert(locIndex);
            LinTSBreakLoc.insert(make_pair(curIndex, resHash));
        } else {
            unordered_set<int>& resHash = LinTSBreakLoc[curIndex];
            resHash.insert(locIndex);
        }
    }
    if (linTSLocConstrants.find(curIndex) == linTSLocConstrants.end()) {
        map<int, int> resIdMap;
        resIdMap.insert(
            make_pair(curLinTS->SearchLocIndex(curLocName), locIndex));
        LocIdMap.insert(make_pair(curIndex, resIdMap));
        map<int, vector<C_Polyhedron*>> resCS;
        map<int, C_Polyhedron*> resEquals;
        map<int, vector<bool>> resFlags;
        pair<vector<C_Polyhedron*>, vector<bool>> resPairs =
            state->getConstraints();
        map<int, vector<C_Polyhedron*>> resAssert;
        resCS.insert(make_pair(locIndex, resPairs.first));
        linTSLocConstrants.insert(make_pair(curIndex, resCS));
        resFlags.insert(make_pair(locIndex, resPairs.second));
        linTSLocNondetFlags.insert(make_pair(curIndex, resFlags));
        resEquals.insert(make_pair(locIndex, state->getVarEqualities()));
        // cout << *state->getVarEqualities() << endl;
        // cout << "[here]" << endl;
        // cout << curIndex << " " << locIndex << endl;
        linTSLocEqualities.insert(make_pair(curIndex, resEquals));
        resAssert.insert(make_pair(locIndex, state->getAssertions()));
        linTSAssertion.insert(make_pair(curIndex, resAssert));
    } else {
        map<int, int>& resIdMap = LocIdMap[curIndex];
        resIdMap.insert(
            make_pair(curLinTS->SearchLocIndex(curLocName), locIndex));
        map<int, vector<C_Polyhedron*>>& resCS = linTSLocConstrants[curIndex];
        map<int, C_Polyhedron*>& resEquals = linTSLocEqualities[curIndex];
        map<int, vector<bool>>& resFlags = linTSLocNondetFlags[curIndex];
        pair<vector<C_Polyhedron*>, vector<bool>> resPairs =
            state->getConstraints();
        map<int, vector<C_Polyhedron*>>& resAssert = linTSAssertion[curIndex];
        resFlags.insert(make_pair(locIndex, resPairs.second));
        resCS.insert(make_pair(locIndex, resPairs.first));
        resEquals.insert(make_pair(locIndex, state->getVarEqualities()));
        resAssert.insert(make_pair(locIndex, state->getAssertions()));
    }
    return;
}
void CParser::TraverseProgramStmt(Stmt* stmt,
                                  ProgramState* curState,
                                  Stmt* nextStmt,
                                  bool processing) {
    if (curState->CheckEnd())
        return;
    if (stmt == nullptr) {
        if (processing)
            ProcessProgramState(curState);
        return;
    }
    cout << "[curStmt] " << stmt->getStmtClassName() << endl;
    // TODO: All conditional expressions may need to be preprocessed. The
    // purpose of the preprocessing function is to safely convert them into
    // Expr* that can be transformed into linear expressions.
    if (isa<IfStmt>(stmt)) {
        IfStmt* ifstmt = dyn_cast<IfStmt>(stmt);
        Expr* cond = PreProcessExpr(ifstmt->getCond(), curState);
        Stmt* thenBranch = ifstmt->getThen();
        Stmt* elseBranch = ifstmt->getElse();
        pair<vector<C_Polyhedron*>, vector<bool>> Pairs =
            curState->getConstraints();
        ProgramState* branchState = new ProgramState(curState);
        branchState->MergeWithConstraints(Pairs.first, Pairs.second);
        branchState->setLoopIndex(curState->getLoopIndex());
        branchState->addConstraint(CreateUnaryOperator(cond, UO_LNot));
        vector<ProgramState*> splitState = branchState->getSplitProgramState();
        if (elseBranch) {
            for (int i = 0; i < splitState.size(); i++) {
                splitState[i]->setLocIndex(globalLocCount);
                TraverseProgramStmt(elseBranch, splitState[i], nextStmt,
                                    processing);
            }
        } else {
            for (int i = 0; i < splitState.size(); i++) {
                splitState[i]->setLocIndex(globalLocCount);
                TraverseProgramStmt(nextStmt, splitState[i], NULL, processing);
            }
        }
        curState->addConstraint(cond);
        splitState = curState->getSplitProgramState();
        for (int i = 0; i < splitState.size(); i++) {
            splitState[i]->setLocIndex(globalLocCount);
            TraverseProgramStmt(thenBranch, splitState[i], nextStmt,
                                processing);
        }
        return;
    } else if (isa<WhileStmt>(stmt)) {
        WhileStmt* whilestmt = dyn_cast<WhileStmt>(stmt);
        Stmt* whileBody = whilestmt->getBody();
        Expr* cond = PreProcessExpr(whilestmt->getCond(), curState);
        ProgramState* exitState = new ProgramState(curState);
        ProgramState* inWhileState = new ProgramState(curState);
        pair<vector<C_Polyhedron*>, vector<bool>> Pairs =
            curState->TransformExprIntoDisjunctiveForm(cond, false);
        vector<ProgramState*> splitState = curState->getSplitProgramState();
        assert(splitState.size() == 1);
        exitState->addConstraint(Pairs.first);
        exitState->addConstraint(curState->getConstraints().first);
        Pairs = curState->TransformExprIntoDisjunctiveForm(cond, true);
        curState->addConstraint(Pairs.first);
        if (!curState->CheckEnd()) {
            LinTS* emptylinTS = new LinTS();
            inWhileState->clearVarState();
            inWhileState->setIntoLoop(++LoopCount);
            exitState->setLoopIndex(LoopCount);
            curState->setLoopIndex(LoopCount);
            linTSInit.insert(make_pair(LoopCount, curState->getInitPolys()));
            linTSMap.insert(make_pair(LoopCount, emptylinTS));
            pair<vector<C_Polyhedron*>, vector<bool>> tmpPairs =
                inWhileState->TransformExprIntoDisjunctiveForm(cond, false);
            loopExitCond.insert(make_pair(LoopCount, tmpPairs.first));
            loopExitFlags.insert(make_pair(LoopCount, tmpPairs.second));
            tmpPairs =
                inWhileState->TransformExprIntoDisjunctiveForm(cond, true);
            inWhileState->addConstraint(tmpPairs.first);
            if (!inWhileState->CheckEnd()) {
                splitState = inWhileState->getSplitProgramState();
                for (int i = 0; i < splitState.size(); i++) {
                    splitState[i]->setLocIndex(globalLocCount);
                    TraverseProgramStmt(whileBody, splitState[i], NULL, true);
                }
                ComputeLinTSInv(inWhileState->getLoopIndex(), curState);
                splitState = curState->getSplitProgramState();
                for (int i = 0; i < splitState.size(); i++) {
                    splitState[i]->setLocIndex(globalLocCount);
                    TraverseProgramStmt(nextStmt, splitState[i], NULL,
                                        processing);
                }
            }
        }
        if (!exitState->CheckEnd()) {
            splitState = exitState->getSplitProgramState();
            for (int i = 0; i < splitState.size(); i++) {
                splitState[i]->setLocIndex(globalLocCount);
                TraverseProgramStmt(nextStmt, splitState[i], NULL, processing);
            }
        }
        return;
    } else if (isa<DoStmt>(stmt)) {
        DoStmt* dostmt = dyn_cast<DoStmt>(stmt);
        WhileStmt* whilestmt =
            CreateWhileStmt(dostmt->getBody(), dostmt->getCond());
        TraverseProgramStmt(dostmt->getBody(), curState, whilestmt, processing);
        return;
    } else if (isa<ForStmt>(stmt)) {
        ForStmt* forstmt = dyn_cast<ForStmt>(stmt);
        SmallVector<Stmt*, 8> stmtList;
        stmtList.push_back(forstmt->getBody());
        stmtList.push_back(forstmt->getInc());
        WhileStmt* whilestmt =
            CreateWhileStmt(CreateCompoundStmt(stmtList), forstmt->getCond());
        IncStmts.insert(make_pair(LoopCount + 1, forstmt->getInc()));
        TraverseProgramStmt(forstmt->getInit(), curState, whilestmt,
                            processing);
        return;
    } else if (isa<ContinueStmt>(stmt)) {
        ContinueStmt* continuestmt = dyn_cast<ContinueStmt>(stmt);
        int curLoopId = curState->getLoopIndex();
        if (IncStmts.find(curLoopId) != IncStmts.end())
            TraverseProgramStmt(IncStmts[curLoopId], curState, NULL,
                                processing);
        else
            TraverseProgramStmt(NULL, curState, NULL, processing);
        return;
    } else if (isa<BreakStmt>(stmt)) {
        BreakStmt* breakstmt = dyn_cast<BreakStmt>(stmt);
        curState->setBreakFlag();
        TraverseProgramStmt(NULL, curState, NULL, processing);
        return;
    } else if (isa<ReturnStmt>(stmt)) {
        ReturnStmt* returnstmt = dyn_cast<ReturnStmt>(stmt);
        delete curState;
        return;
    } else if (isa<CompoundStmt>(stmt)) {
        CompoundStmt* compound = dyn_cast<CompoundStmt>(stmt);
        SmallVector<Stmt*, 8> stmtList;
        Stmt* firstStmt = NULL;
        for (Stmt* stmt : compound->body()) {
            if (firstStmt == NULL)
                firstStmt = stmt;
            else
                stmtList.push_back(stmt);
        }
        if (nextStmt)
            stmtList.push_back(nextStmt);
        TraverseProgramStmt(firstStmt, curState, CreateCompoundStmt(stmtList),
                            processing);
        return;
    } else if (isa<DeclStmt>(stmt)) {
        DeclStmt* decl = dyn_cast<DeclStmt>(stmt);
        for (Decl* singleDecl : decl->getDeclGroup()) {
            if (isa<VarDecl>(singleDecl)) {
                VarDecl* singleVarDecl = dyn_cast<VarDecl>(singleDecl);
                string varName = singleVarDecl->getNameAsString();
                Expr* varInit = singleVarDecl->getInit();
                if (varInit) {
                    varInit = PreProcessExpr(varInit, curState);
                    if (isa<CallExpr>(varInit)) {
                        curState->ProcessAssign(
                            CreateVarRefExpr(singleVarDecl));
                    } else {
                        BinaryOperator* initExpr = CreateBinaryOperator(
                            CreateVarRefExpr(singleVarDecl),
                            varInit->IgnoreParenCasts(), BO_Assign,
                            singleVarDecl->getType());
                        curState->ProcessAssign(initExpr);
                    }
                } else {
                    curState->ProcessAssign(CreateVarRefExpr(singleVarDecl));
                }
            } else {
                throw runtime_error(
                    "We currently do not support handling declarations other "
                    "than variable declarations inside functions (such as "
                    "defining another function within a function). This would "
                    "complicate the code analysis and introduce unnecessary "
                    "logic (for the time being).");
            }
        }
        TraverseProgramStmt(nextStmt, curState, NULL, processing);
        return;
    } else if (isa<BinaryOperator>(stmt)) {
        BinaryOperator* binary = dyn_cast<BinaryOperator>(stmt);
        Expr* proStmt = PreProcessExpr(binary, curState);
        TraverseProgramStmt(nextStmt, curState, NULL, processing);
        return;
    } else if (isa<CallExpr>(stmt)) {
        CallExpr* call = dyn_cast<CallExpr>(stmt);
        PreProcessExpr(call, curState);
        TraverseProgramStmt(nextStmt, curState, NULL, processing);
        return;
    } else if (isa<UnaryOperator>(stmt)) {
        UnaryOperator* unary = dyn_cast<UnaryOperator>(stmt);
        PreProcessExpr(unary->IgnoreParenCasts(), curState);
        TraverseProgramStmt(nextStmt, curState, NULL, processing);
        return;
    } else if (isa<DeclRefExpr>(stmt)) {
        TraverseProgramStmt(nextStmt, curState, NULL, processing);
        return;
    }
    throw runtime_error(
        "The current Stmt type being processed exceeds the predefined range of "
        "Stmt types.");
    return;
}