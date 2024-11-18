#ifndef CPARSERPROGRAMSTATE_H_
#define CPARSERPROGRAMSTATE_H_
#include <map>
#include <unordered_set>
#include <utility>
#include "ParserUtility.h"
// This class primarily describes the changes in program state during execution.
class ProgramState {
   public:
    ProgramState();
    ProgramState(ProgramState* state);
    void ProcessAssign(clang::Expr* Expr);

    bool IsInLoop() { return intoLoop; }

    Parma_Polyhedra_Library::C_Polyhedron* SummaryInitPoly();

    void MergeWithConstraints(
        std::vector<Parma_Polyhedra_Library::C_Polyhedron*> polys,std::vector<bool> flags);

    std::pair<std::vector<Parma_Polyhedra_Library::C_Polyhedron*>,
              std::vector<bool>>
    TransformExprIntoDisjunctiveForm(clang::Expr* expr, bool logic);
    std::vector<Parma_Polyhedra_Library::C_Polyhedron*>
    TransformExprIntoConstraints(clang::Expr* expr, bool logic);

    Parma_Polyhedra_Library::Linear_Expression TransformExprIntoLinExpr(
        clang::Expr* expr);

    void addAssertion(std::vector<Parma_Polyhedra_Library::C_Polyhedron*> polys);
    void addConstraint(clang::Expr* expr);
    void addConstraint(std::vector<Parma_Polyhedra_Library::C_Polyhedron*> polys);
    void clearVarState();
    void clearConstraints() {
        varConstraints.clear();
        return;
    }

    void setBreakFlag() {
        breakFlag = true;
        return;
    }
    void setIntoLoop(int cnt) {
        intoLoop = true;
        loopIndex = cnt;
        return;
    }
    void setEnd() { endFlag = true; }
    void setLoopIndex(int cnt) {
        loopIndex = cnt;
        return;
    }
    void setLocIndex(int& cnt) {
        locIndex = cnt;
        cnt++;
        return;
    }
    bool CheckEnd() { return endFlag; }
    int getLoopIndex() { return loopIndex; }
    int getLocIndex() { return locIndex; }
    std::string getLocName() {
        return std::string("Loc") + std::to_string(locIndex);
    }
    std::vector<std::string>& getVarList() { return varList; }
    int getVarNum() { return varNum; }
    std::pair<std::vector<Parma_Polyhedra_Library::C_Polyhedron*>,
              std::vector<bool>> getConstraints();
    Parma_Polyhedra_Library::C_Polyhedron* getVarEqualities();
    std::vector<Parma_Polyhedra_Library::C_Polyhedron*>
    getCompleteConstraints();
    std::vector<Parma_Polyhedra_Library::C_Polyhedron*> getInitPolys();
    std::vector<Parma_Polyhedra_Library::C_Polyhedron*> getAssertions() {return assertions;}
    std::vector<ProgramState*> getSplitProgramState();
    bool getBreakFlag() {return breakFlag;}
   private:
    std::vector<std::string> varList;
    std::map<std::string, int> varNameMap;
    std::unordered_set<std::string> varHash;
    int varNum;
    std::map<std::string, Parma_Polyhedra_Library::Linear_Expression> varState;

    std::vector<Parma_Polyhedra_Library::Constraint_System> varConstraints;
    std::vector<bool> nondetConstraints;
    std::vector<Parma_Polyhedra_Library::C_Polyhedron*> assertions;
    bool intoLoop;
    int loopIndex;
    int locIndex;
    bool breakFlag;
    bool endFlag;
};

#endif