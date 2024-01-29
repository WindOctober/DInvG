cmake_minimum_required(VERSION 3.10)

project(lstingX LANGUAGES CXX)

# Add include directories
find_package(BISON)
find_package(FLEX)
BISON_TARGET(LinTSParser LinTS.y ${CMAKE_CURRENT_BINARY_DIR}/LinTSParser.cpp DEFINES_FILE ${CMAKE_CURRENT_BINARY_DIR}/parser.h)
FLEX_TARGET(LinTSLexer LinTS.l ${CMAKE_CURRENT_BINARY_DIR}/LinTSLexer.cpp)
ADD_FLEX_BISON_DEPENDENCY(LinTSLexer LinTSParser)

find_library(Z3_LIBRARY NAMES z3 PATHS ../z3/build)
find_path(Z3_INCLUDE_DIR z3++.h)
include_directories(${Z3_INCLUDE_DIR})

include_directories(${CMAKE_CURRENT_SOURCE_DIR} ${CMAKE_CURRENT_BINARY_DIR})
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ")
# Add source files
set(SRC_FILES
    ${BISON_LinTSParser_OUTPUTS}
    ${FLEX_LinTSLexer_OUTPUTS}
    Clump.cpp
    Context.cpp
    DisequalityStore.cpp
    Expression.cpp
    ExpressionStore.cpp
    funcs.cpp
    LinExpr.cpp
    LinTransform.cpp
    Location.cpp
    MatrixStore.cpp
    PolyStore.cpp
    PolyUtils.cpp
    Rational.cpp
    LinTS.cpp
    SparseLinExpr.cpp
    Timer.cpp
    TransitionRelation.cpp
    var-info.cpp
    Elimination.cpp
    Tree.cpp
    ToolUtils.cpp
    Macro.cpp
    lstingx.cpp
)


# create static library target
add_library(lstingx STATIC ${SRC_FILES})
target_link_libraries(lstingx PUBLIC -lppl -lgmpxx -lgmp ${Z3_LIBRARY})
target_compile_options(lstingx PRIVATE -g )

# create executable target
add_executable(lstingX lstingx.cpp)
target_compile_definitions(lstingX PRIVATE USE_LSTINGX_MAIN)
target_link_libraries(lstingX PUBLIC lstingx ${Z3_LIBRARY})
set_target_properties(lstingX PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${CMAKE_SOURCE_DIR}/bin)
