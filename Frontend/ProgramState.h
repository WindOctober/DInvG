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

    void ComputeProgramInv();
    void UpdateByStateSummary(ProgramState* updateState);

    bool CheckAssertion();
    bool CheckInconsistentCond(clang::Expr* cond);

    bool IsInLoop() { return intoLoop; }

    Parma_Polyhedra_Library::C_Polyhedron* SummaryInitPoly();

    void addConstraint(clang::Expr* expr);

    void setBreakFlag() {
        breakFlag = true;
        return;
    }
    void setIntoLoop(int cnt) {
        intoLoop = true;
        loopNo = cnt;
        return;
    }
    void setInitPoly(Parma_Polyhedra_Library::C_Polyhedron* poly);

   private:
    std::vector<std::string> varList;
    std::unordered_set<std::string> varHash;
    int varNum;
    std::map<std::string, Parma_Polyhedra_Library::Linear_Expression> varState;
    std::vector<Parma_Polyhedra_Library::Linear_Expression> varConstraints;
    bool intoLoop;
    int loopNo;
    bool breakFlag;
    Parma_Polyhedra_Library::C_Polyhedron* initPoly;
};

#endif