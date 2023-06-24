include_directories(${LLVM_INCLUDE_FLAGS})
include_directories(${CMAKE_SOURCE_DIR}/Stingx)
set(SOURCES Library.cpp ACSLComment.cpp Variable.cpp TransitionSystem.cpp CFGVisitor.cpp)
add_library(Frontend ${SOURCES})