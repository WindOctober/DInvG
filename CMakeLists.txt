cmake_minimum_required(VERSION 3.16.3)

project(PowerInv)
add_executable(Inv ${CMAKE_SOURCE_DIR}/main.cpp)
set(EXECUTABLE_OUTPUT_PATH "${CMAKE_SOURCE_DIR}")
include_directories(${CMAKE_SOURCE_DIR})
include_directories(${CMAKE_SOURCE_DIR}/src/)
#Adjust LLVM_CONFIG

set(LLVM_CONFIG "llvm-config" CACHE PATH "Path to llvm-config executable")
find_program(LLVM_CONFIG_EXECUTABLE ${LLVM_CONFIG})
if(NOT LLVM_CONFIG_EXECUTABLE)
  message(FATAL_ERROR "llvm-config executable not found. Set LLVM_CONFIG to the path to llvm-config executable.")
endif()

execute_process(COMMAND ${LLVM_CONFIG} --libs --system-libs OUTPUT_VARIABLE LLVM_LIBRARY)
string(REPLACE "\n" "" LLVM_LIBRARY ${LLVM_LIBRARY})

set(CLANG_LIBS
  -Wl,--start-group
  -lclang
  -lclangAST
  -lclangAnalysis
  -lclangBasic
  -lclangDriver
  -lclangEdit
  -lclangIndex
  -lclangFrontend
  -lclangFrontendTool
  -lclangLex
  -lclangSupport
  -lclangParse
  -lclangSema
  -lclangEdit
  -lclangASTMatchers
  -lclangRewrite
  -lclangRewriteFrontend
  -lclangStaticAnalyzerFrontend
  -lclangStaticAnalyzerCheckers
  -lclangStaticAnalyzerCore
  -lclangSerialization
  -lclangToolingCore
  -lclangTooling
  -lLLVM-17
  -lLLVMSupport
  -Wl,--end-group
)



execute_process(COMMAND ${LLVM_CONFIG} --libs --system-libs --ldflags OUTPUT_VARIABLE LLVM_LD_FLAGS)
execute_process(COMMAND ${LLVM_CONFIG} --cxxflags OUTPUT_VARIABLE LLVM_CXX_FLAGS)
execute_process(COMMAND ${LLVM_CONFIG} --includedir OUTPUT_VARIABLE LLVM_INCLUDE_FLAGS)
string(REPLACE "\n" "" LLVM_INCLUDE_FLAGS ${LLVM_INCLUDE_FLAGS})
string(REPLACE "\n" "" LLVM_CXX_FLAGS ${LLVM_CXX_FLAGS})
string(REPLACE "\n" "" LLVM_LD_FLAGS ${LLVM_LD_FLAGS})
string(REPLACE "-L" "" LLVM_LD_PATH ${LLVM_LD_FLAGS})

link_directories(${LLVM_LD_PATH})
include_directories(${LLVM_INCLUDE_FLAGS})
target_link_libraries(Inv ${CLANG_LIBS})

#set CXX flags

set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS}  ${LLVM_LD_FLAGS}")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DENABLE_LLVM_SHARED=1 ${LLVM_CXX_FLAGS}")