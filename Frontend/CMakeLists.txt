include_directories(${LLVM_INCLUDE_FLAGS})
include_directories(${CMAKE_SOURCE_DIR}/Stingx)
set(SOURCES CParser.cpp ParserUtility.cpp ProgramState.cpp)
add_library(Frontend ${SOURCES})