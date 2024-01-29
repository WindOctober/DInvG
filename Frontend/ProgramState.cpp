#include "ProgramState.h"
#include <stdexcept>
#include <utility>
#include "LinTS.h"
#include "ParserUtility.h"
using namespace std;
using namespace clang;
using namespace llvm;
using namespace Parma_Polyhedra_Library;
ProgramState::ProgramState() {
    varNum = 0;
    intoLoop = false;
    breakFlag = false;
    endFlag = false;
    varList.clear();
    varHash.clear();
    varState.clear();
    varConstraints.clear();
    return;
}

ProgramState::ProgramState(ProgramState* state) {
    varNum = state->varNum;
    intoLoop = state->intoLoop;
    loopIndex = state->loopIndex;
    breakFlag = state->breakFlag;
    endFlag = state->endFlag;
    varConstraints.clear();
    varList.clear();
    varNameMap.clear();
    varState.clear();
    varHash.clear();
    for (int i = 0; i < state->varList.size(); i++)
        varList.push_back(state->varList[i]);
    for (auto p : state->varNameMap)
        varNameMap.insert(p);
    for (auto s : state->varHash)
        varHash.insert(s);
    for (auto p : state->varState)
        varState.insert(p);
    return;
}
void ProgramState::ProcessAssign(Expr* expr) {
    if (isa<DeclRefExpr>(expr)) {
        DeclRefExpr* declref = dyn_cast<DeclRefExpr>(expr);
        VarDecl* var = dyn_cast<VarDecl>(declref->getDecl());
        if (var == nullptr) {
            throw runtime_error("");
        }
        string varName = var->getNameAsString();
        if (varHash.find(varName) == varHash.end()) {
            varHash.insert(varName);
            varList.push_back(varName);
            varNameMap.insert(make_pair(varName, varNum));
            varState.insert(make_pair(varName, Variable(varNum)));
            varNum++;
        }
        return;
    }
    BinaryOperator* binary = dyn_cast<BinaryOperator>(expr);
    if (binary->getOpcode() == BO_Assign) {
        Expr* leftValue = binary->getLHS();
        if (isa<DeclRefExpr>(leftValue)) {
            DeclRefExpr* decl = dyn_cast<DeclRefExpr>(leftValue);
            string varName = decl->getDecl()->getNameAsString();
            if (varHash.find(varName) == varHash.end()) {
                varHash.insert(varName);
                varList.push_back(varName);
                varNameMap.insert(make_pair(varName, varNum));
                varState.insert(make_pair(varName, Variable(varNum)));
                varNum++;
            }
            if (!isa<CallExpr>(binary->getRHS()))
                varState[varName] = TransformExprIntoLinExpr(binary->getRHS());
            else{
                CallExpr* call=dyn_cast<CallExpr>(binary->getRHS());
                FunctionDecl* func=call->getDirectCallee();
                string funcName=func->getNameAsString();
                if (funcName.find("uchar")!=funcName.npos){
                    vector<C_Polyhedron*> polys;
                    C_Polyhedron* poly=new C_Polyhedron(varNum,UNIVERSE);
                    poly->add_constraint(Variable(varNameMap[varName])>=0);
                    poly->add_constraint(Variable(varNameMap[varName])<=(2<<8-1));
                    polys.push_back(poly);
                    addConstraint(polys);
                }
                else if (funcName.find("uint")!=funcName.npos){
                    vector<C_Polyhedron*> polys;
                    C_Polyhedron* poly=new C_Polyhedron(varNum,UNIVERSE);
                    poly->add_constraint(Variable(varNameMap[varName])>=0);
                    polys.push_back(poly);
                    addConstraint(polys);
                }
            }
        } else {
            throw runtime_error(
                "Currently, other types of l-values are not supported, "
                "apart from variable references.");
        }
        return;
    }
    return;
}

void ProgramState::MergeWithConstraints(vector<C_Polyhedron*> polys,
                                        vector<bool> flags) {
    if (varConstraints.size() == 0) {
        for (int i = 0; i < polys.size(); i++) {
            Constraint_System tmpCS = polys[i]->minimized_constraints();
            varConstraints.push_back(tmpCS);
            nondetConstraints.push_back(flags[i]);
        }
        return;
    }
    vector<Constraint_System> newVecConstraints;
    vector<bool> newNondetFlags;
    for (int i = 0; i < varConstraints.size(); i++) {
        for (int j = 0; j < polys.size(); j++) {
            Constraint_System resCS = varConstraints[i];
            for (Constraint cs : polys[j]->minimized_constraints()) {
                resCS.insert(cs);
            }
            newVecConstraints.push_back(resCS);
            newNondetFlags.push_back(nondetConstraints[i] || flags[j]);
        }
    }
    varConstraints = newVecConstraints;
    nondetConstraints = newNondetFlags;
    return;
}

pair<vector<C_Polyhedron*>, vector<bool>>
ProgramState::TransformExprIntoDisjunctiveForm(Expr* expr, bool logic) {
    vector<C_Polyhedron*> leftPolys;
    vector<C_Polyhedron*> rightPolys;
    vector<bool> leftFlags;
    vector<bool> rightFlags;
    if (isa<BinaryOperator>(expr)) {
        BinaryOperator* binary = dyn_cast<BinaryOperator>(expr);
        if (binary->getOpcode() == BO_LAnd) {
            pair<vector<C_Polyhedron*>, vector<bool>> leftPair =
                TransformExprIntoDisjunctiveForm(binary->getLHS(), logic);
            pair<vector<C_Polyhedron*>, vector<bool>> rightPairs =
                TransformExprIntoDisjunctiveForm(binary->getRHS(), logic);
            leftPolys = leftPair.first;
            leftFlags = leftPair.second;
            rightPolys = rightPairs.first;
            rightFlags = rightPairs.second;
            if (logic)
                return make_pair(MergeTwoPolyVector(leftPolys, rightPolys),
                                 MergeTwoBoolVector(leftFlags, rightFlags));
            else
                return make_pair(ConnectTwoPolyVector(leftPolys, rightPolys),
                                 ConnectTwoBoolVector(leftFlags, rightFlags));

        } else if (binary->getOpcode() == BO_LOr) {
            pair<vector<C_Polyhedron*>, vector<bool>> leftPair =
                TransformExprIntoDisjunctiveForm(binary->getLHS(), logic);
            pair<vector<C_Polyhedron*>, vector<bool>> rightPairs =
                TransformExprIntoDisjunctiveForm(binary->getRHS(), logic);
            leftPolys = leftPair.first;
            leftFlags = leftPair.second;
            rightPolys = rightPairs.first;
            rightFlags = rightPairs.second;
            if (!logic)
                return make_pair(MergeTwoPolyVector(leftPolys, rightPolys),
                                 MergeTwoBoolVector(leftFlags, rightFlags));
            else
                return make_pair(ConnectTwoPolyVector(leftPolys, rightPolys),
                                 ConnectTwoBoolVector(leftFlags, rightFlags));
        }
    } else if (isa<UnaryOperator>(expr)) {
        UnaryOperator* unary = dyn_cast<UnaryOperator>(expr);
        if (unary->getOpcode() == UO_LNot) {
            return TransformExprIntoDisjunctiveForm(unary->getSubExpr(),
                                                    !logic);
        }
    } else if (isa<DeclRefExpr>(expr)) {
        C_Polyhedron* trivial = new C_Polyhedron(varNum, UNIVERSE);
        vector<C_Polyhedron*> polys;
        vector<bool> flags;
        flags.push_back(true);
        polys.push_back(trivial);
        return make_pair(polys, flags);
    } else if (isa<CallExpr>(expr)) {
        CallExpr* call = dyn_cast<CallExpr>(expr);
        FunctionDecl* funcdecl = call->getDirectCallee();
        string funcName = funcdecl->getNameAsString();
        if (funcName.find("__VERIFIER_nondet_") != funcName.npos) {
            C_Polyhedron* trivial = new C_Polyhedron(varNum, UNIVERSE);
            vector<C_Polyhedron*> polys;
            vector<bool> flags;
            flags.push_back(true);
            polys.push_back(trivial);
            return make_pair(polys, flags);
        }
    } else if (isa<ParenExpr>(expr)) {
        ParenExpr* paren = dyn_cast<ParenExpr>(expr);
        return TransformExprIntoDisjunctiveForm(paren->getSubExpr(), logic);
    } else if (isa<IntegerLiteral>(expr)) {
        IntegerLiteral* integer = dyn_cast<IntegerLiteral>(expr);
        APInt apIntVal = integer->getValue();
        uint64_t uintVal = apIntVal.getLimitedValue();
        if (uintVal <= static_cast<uint64_t>(numeric_limits<int>::max())) {
            int intValue = static_cast<int>(uintVal);
            vector<C_Polyhedron*> polys;
            if (logic)
                if (intValue == 0)
                    polys.push_back(new C_Polyhedron(varNum, EMPTY));
                else
                    polys.push_back(new C_Polyhedron(varNum, UNIVERSE));
            else
                if (intValue != 0)
                    polys.push_back(new C_Polyhedron(varNum, EMPTY));
                else
                    polys.push_back(new C_Polyhedron(varNum, UNIVERSE));
            vector<bool> flags;
            flags.push_back(false);
            return make_pair(polys, flags);
        } else {
            throw runtime_error("The value exceeds the range of an int.");
        }
    } else {
        throw runtime_error(
            "In conditional expressions, there are operators other than binary "
            "and unary operators.");
    }
    if (isa<BinaryOperator>(expr)) {
        vector<C_Polyhedron*> polys =
            TransformExprIntoConstraints(expr->IgnoreParenCasts(), logic);
        vector<bool> flags(polys.size(), false);
        return make_pair(polys, flags);
    }
    throw runtime_error(
        "During the process of transforming conditional expressions, the "
        "final base clauses do not correspond to the common binary "
        "operator conditional expressions.");
}

vector<C_Polyhedron*> ProgramState::TransformExprIntoConstraints(Expr* expr,
                                                                 bool logic) {
    BinaryOperator* binary = dyn_cast<BinaryOperator>(expr);
    BinaryOperatorKind kind = binary->getOpcode();
    if (!logic) {
        if (kind == BO_LE)
            kind = BO_GT;
        else if (kind == BO_LT)
            kind = BO_GE;
        else if (kind == BO_GE)
            kind = BO_LT;
        else if (kind == BO_GT)
            kind = BO_LE;
        else if (kind == BO_EQ)
            kind = BO_NE;
        else if (kind == BO_NE)
            kind = BO_EQ;
        else {
            throw runtime_error(
                "The constraints can only involve the six common binary "
                "operators: <, <=, >, >=, ==, !=.");
        }
    }
    Linear_Expression left = TransformExprIntoLinExpr(binary->getLHS());
    Linear_Expression right = TransformExprIntoLinExpr(binary->getRHS());
    vector<C_Polyhedron*> polys;
    Constraint cs;
    if (kind == BO_GT)
        cs = (left - 1) >= right;
    else if (kind == BO_LT)
        cs = (left + 1) <= right;
    else if (kind == BO_GE)
        cs = left >= right;
    else if (kind == BO_LE)
        cs = left <= right;
    else if (kind == BO_EQ)
        cs = left == right;
    else {
        cs = (left - 1) >= right;
        if (cs.is_tautological())
            polys.push_back(new C_Polyhedron(varNum, UNIVERSE));
        else if (cs.is_inconsistent())
            polys.push_back(new C_Polyhedron(varNum, EMPTY));
        else {
            C_Polyhedron* poly = new C_Polyhedron(varNum, UNIVERSE);
            poly->add_constraint(cs);
            polys.push_back(poly);
        }
        cs = (left + 1) <= right;
    }
    if (cs.is_tautological())
        polys.push_back(new C_Polyhedron(varNum, UNIVERSE));
    else if (cs.is_inconsistent())
        polys.push_back(new C_Polyhedron(varNum, EMPTY));
    else {
        C_Polyhedron* poly = new C_Polyhedron(varNum, UNIVERSE);
        poly->add_constraint(cs);
        polys.push_back(poly);
    }
    return polys;
}
Linear_Expression ProgramState::TransformExprIntoLinExpr(Expr* expr) {
    expr = expr->IgnoreParenCasts()->IgnoreImplicit();
    if (isa<BinaryOperator>(expr)) {
        BinaryOperator* binary = dyn_cast<BinaryOperator>(expr);
        cout<<binary->getOpcode()<<endl;
        if (binary->getOpcode() == BO_Add) {
            Linear_Expression left = TransformExprIntoLinExpr(binary->getLHS());
            Linear_Expression right =
                TransformExprIntoLinExpr(binary->getRHS());
            return (left + right);
        } else if (binary->getOpcode() == BO_Sub) {
            Linear_Expression left = TransformExprIntoLinExpr(binary->getLHS());
            Linear_Expression right =
                TransformExprIntoLinExpr(binary->getRHS());
            return (left - right);
        } else if (binary->getOpcode() == BO_Mul) {
            Linear_Expression left = TransformExprIntoLinExpr(binary->getLHS());
            Linear_Expression right =
                TransformExprIntoLinExpr(binary->getRHS());

            if (left.all_homogeneous_terms_are_zero()) {
                Coefficient constant = left.inhomogeneous_term();
                return constant * right;
            } else if (right.all_homogeneous_terms_are_zero()) {
                Coefficient constant = right.inhomogeneous_term();
                return constant * left;
            }
            throw runtime_error(
                "Only linear combinations such as a constant multiplied by a "
                "variable are supported");
        } else {
            throw runtime_error(
                "Currently, arithmetic operations other than the three basic "
                "operations of addition, subtraction, and multiplication are "
                "not supported.");
        }
    } else if (isa<UnaryOperator>(expr)) {
        UnaryOperator* unary = dyn_cast<UnaryOperator>(expr);
        unary = dyn_cast<UnaryOperator>(unary->IgnoreParenCasts());
        if (unary->getOpcode() == UO_Minus) {
            return -TransformExprIntoLinExpr(unary->getSubExpr());
        } else if (unary->getOpcode() == UO_Plus) {
            return TransformExprIntoLinExpr(unary->getSubExpr());
        }
    } else if (isa<DeclRefExpr>(expr)) {
        DeclRefExpr* decl = dyn_cast<DeclRefExpr>(expr);
        string declName = decl->getDecl()->getNameAsString();
        if (varState.find(declName) == varState.end()) {
            throw runtime_error(
                "When processing conditional expressions, there are undefined "
                "variables.");
        }
        return varState[declName];
    } else if (isa<IntegerLiteral>(expr)) {
        IntegerLiteral* integer = dyn_cast<IntegerLiteral>(expr);
        APInt apIntVal = integer->getValue();
        uint64_t uintVal = apIntVal.getLimitedValue();
        if (uintVal <= static_cast<uint64_t>(numeric_limits<int>::max())) {
            int intValue = static_cast<int>(uintVal);
            return Linear_Expression(intValue);
        } else {
            throw runtime_error("The value exceeds the range of an int.");
        }
    } else if (isa<ImplicitCastExpr>(expr)) {
        ImplicitCastExpr* implicit = dyn_cast<ImplicitCastExpr>(expr);
        return TransformExprIntoLinExpr(implicit->getSubExpr());
    }
    throw runtime_error(
        "During the conversion to linear expressions, an unrecognizable "
        "Clang expression was encountered.");
    return Linear_Expression(0);
}
void ProgramState::clearVarState() {
    for (pair<string, Linear_Expression> varPair : varState) {
        string var = varPair.first;
        varState[var] = Variable(varNameMap[var]);
    }
    return;
}

void ProgramState::addAssertion(vector<C_Polyhedron*> polys){
    assertions.insert(assertions.end(),polys.begin(),polys.end());
    return;
}
void ProgramState::addConstraint(Expr* expr) {
    pair<vector<C_Polyhedron*>, vector<bool>> pairs =
        TransformExprIntoDisjunctiveForm(expr->IgnoreParenCasts(), true);
    vector<C_Polyhedron*> Constraints = pairs.first;
    vector<bool> flags = pairs.second;
    MergeWithConstraints(Constraints, flags);
    for (int i = 0; i < varConstraints.size(); i++) {
        C_Polyhedron* poly = new C_Polyhedron(varConstraints[i]);
        if (poly->is_empty()) {
            varConstraints.erase(varConstraints.begin() + i);
            nondetConstraints.erase(nondetConstraints.begin() + i);
            i--;
        }
    }
    if (varConstraints.size() == 0)
        setEnd();
    return;
}
void ProgramState::addConstraint(vector<C_Polyhedron*> polys){
    vector<bool> flags(polys.size(),false);
    MergeWithConstraints(polys, flags);
    for (int i = 0; i < varConstraints.size(); i++) {
        C_Polyhedron* poly = new C_Polyhedron(varConstraints[i]);
        if (poly->is_empty()) {
            varConstraints.erase(varConstraints.begin() + i);
            nondetConstraints.erase(nondetConstraints.begin() + i);
            i--;
        }
    }
    if (varConstraints.size() == 0)
        setEnd();
    return;
}

pair<vector<C_Polyhedron*>, vector<bool>> ProgramState::getConstraints() {
    vector<C_Polyhedron*> resPolys;
    for (int i = 0; i < varConstraints.size(); i++) {
        C_Polyhedron* poly = new C_Polyhedron(varNum, UNIVERSE);
        Constraint_System cs(varConstraints[i]);
        poly->add_constraints(cs);
        resPolys.push_back(poly);
    }
    return make_pair(resPolys, nondetConstraints);
}
C_Polyhedron* ProgramState::getVarEqualities() {
    C_Polyhedron* resPoly = new C_Polyhedron(varNum * 2, UNIVERSE);
    for (pair<string, Linear_Expression> recPair : varState) {
        string var = recPair.first;
        Linear_Expression linexpr = recPair.second;
        int varid = varNameMap[var];
        resPoly->add_constraint((linexpr - Variable(varid + varNum)) == 0);
    }
    return resPoly;
}
vector<C_Polyhedron*> ProgramState::getCompleteConstraints() {
    vector<C_Polyhedron*> ConstraintsPolys = getConstraints().first;
    C_Polyhedron* varPoly = getVarEqualities();
    vector<C_Polyhedron*> varPolys;
    varPolys.push_back(varPoly);
    return MergeTwoPolyVector(ConstraintsPolys, varPolys);
}
vector<C_Polyhedron*> ProgramState::getInitPolys() {
    vector<C_Polyhedron*> polys = getCompleteConstraints();
    for (auto polyhedron : polys) {
        Variables_Set projectSet;
        for (int i = 0; i < varNum; i++)
            projectSet.insert(Variable(i));
        polyhedron->remove_space_dimensions(projectSet);
    }
    return polys;
}

vector<ProgramState*> ProgramState::getSplitProgramState() {
    vector<ProgramState*> res;
    if (varConstraints.size() <= 1) {
        res.push_back(this);
        return res;
    }
    for(int i=0;i<varConstraints.size();i++){
        ProgramState* state=new ProgramState(this);
        vector<C_Polyhedron*> tmpConstraints;
        vector<bool> tmpFlags;
        tmpConstraints.push_back(new C_Polyhedron(varConstraints[i]));
        tmpFlags.push_back(nondetConstraints[i]);
        state->MergeWithConstraints(tmpConstraints,tmpFlags);
        res.push_back(state);
    }
    return res;
}