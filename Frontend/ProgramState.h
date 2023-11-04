#ifndef CPARSERPROGRAMSTATE_H_
#define CPARSERPROGRAMSTATE_H_
#include <map>
#include <utility>
#include <unordered_set>
#include "ParserUtility.h"
// This class primarily describes the changes in program state during execution.
class ProgramState {
   public:
    ProgramState();
    bool inconsistentCond(clang::Expr* cond);
    void addConstraint(clang::Expr* expr);
   private:
    std::vector<std::string> varList;
    std::unordered_set<std::string> varHash;
    int varNum;
};

#endif