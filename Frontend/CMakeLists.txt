set(SOURCES CFGVisitor.cpp)
add_library(Frontend ${SOURCES})
message(${LLVM_INCLUDE_FLAGS})
include_directories(${LLVM_INCLUDE_FLAGS})