#include "ProgramState.h"
using namespace std;
using namespace clang;
using namespace llvm;

ProgramState::ProgramState(){
    varNum=0;
    varList.clear();
    varHash.clear();
}