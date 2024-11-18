include_directories(${LLVM_INCLUDE_FLAGS})
include_directories(${CMAKE_SOURCE_DIR}/Stingx)
set(SOURCES ParserUtility.cpp ProgramState.cpp CParser.cpp)

# Library with DINVG_PROPAGATION defined
add_library(Frontend ${SOURCES})
target_compile_definitions(Frontend PRIVATE DINVG_PROPAGATION)
target_link_libraries(Frontend lstingx)

# Library without DINVG_PROPAGATION defined
add_library(Frontend_NoProp ${SOURCES})
target_link_libraries(Frontend_NoProp lstingx)