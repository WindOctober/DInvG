set(SOURCES CFGVisitor.cpp DNFExpr.cpp)
add_library(Frontend ${SOURCES})
message(${LLVM_INCLUDE_FLAGS})
include_directories(${LLVM_INCLUDE_FLAGS})