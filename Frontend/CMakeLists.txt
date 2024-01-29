include_directories(${LLVM_INCLUDE_FLAGS})
include_directories(${CMAKE_SOURCE_DIR}/Stingx)
set(SOURCES ParserUtility.cpp ProgramState.cpp CParser.cpp)
add_library(Frontend ${SOURCES})