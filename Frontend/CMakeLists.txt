set(SOURCES Variable.cpp TransitionSystem.cpp CFGVisitor.cpp)
add_library(Frontend ${SOURCES})
include_directories(${LLVM_INCLUDE_FLAGS})