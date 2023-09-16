cmake_minimum_required(VERSION 3.10)

project(lstingX LANGUAGES CXX)

# Add include directories

include_directories(${CMAKE_CURRENT_SOURCE_DIR} ${CMAKE_CURRENT_BINARY_DIR})
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ")
# Add source files
set(SRC_FILES
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
    SparseLinExpr.cpp
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


# create static library target
add_library(lstingx STATIC ${SRC_FILES})
target_link_libraries(lstingx PUBLIC -lppl -lgmpxx -lgmp)
target_compile_options(lstingx PRIVATE -g )

# create executable target
add_executable(lstingX lstingx.cpp)
target_compile_definitions(lstingX PRIVATE USE_LSTINGX_MAIN)
target_link_libraries(lstingX PUBLIC lstingx)
set_target_properties(lstingX PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${CMAKE_SOURCE_DIR}/bin)
