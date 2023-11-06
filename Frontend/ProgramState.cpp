#include "ProgramState.h"
using namespace std;
using namespace clang;
using namespace llvm;
using namespace Parma_Polyhedra_Library;
ProgramState::ProgramState() {
    varNum = 0;
    intoLoop = false;
    varList.clear();
    varHash.clear();
    varState.clear();
    varConstraints.clear();
    return;
}


// Subsequent adjustments may be needed for the size of the init_poly space.
C_Polyhedron* ProgramState::SummaryInitPoly() {
    initPoly = new C_Polyhedron(varNum, UNIVERSE);
}