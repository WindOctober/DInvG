cmake_minimum_required(VERSION 3.10)

project(lstingX LANGUAGES CXX)

# Add include directories

include_directories(${CMAKE_CURRENT_SOURCE_DIR} ${CMAKE_CURRENT_BINARY_DIR})

# Add source files
set(SRC_FILES
    Clump.cpp
    Context.cpp
    DisequalityStore.cpp
    DualInvariantMap.cpp
    DualTransitionRelation.cpp
    Expression.cpp
    ExpressionStore.cpp
    funcs.cpp
    InvariantMap.cpp
    LinExpr.cpp
    LinTransform.cpp
    Location.cpp
    MatrixStore.cpp
    PolyStore.cpp
    PolyUtils.cpp
    Rational.cpp
    SparseLinExpr.cpp
    SparseLinTransform.cpp
    System.cpp
    Timer.cpp
    TransitionRelation.cpp
    var-info.cpp
    Elimination.cpp
    Tree.cpp
    ToolUtils.cpp
    Propagation.cpp
    Macro.cpp
    lstingx.cpp
)



add_executable(lstingX ${SRC_FILES})
target_link_libraries(lstingX PUBLIC -lppl -lgmpxx -lgmp)

add_library(lstingx STATIC ${SRC_FILES})
target_link_libraries(lstingx PUBLIC -lppl -lgmpxx -lgmp)
target_compile_options(lstingx PRIVATE -g )
