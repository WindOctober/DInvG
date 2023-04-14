cmake_minimum_required(VERSION 3.16.3)

project(PowerInv)
add_executable(Inv main.cpp)
set(EXECUTABLE_OUTPUT_PATH "${CMAKE_CURRENT_BINARY_DIR}")

#Adjust LLVM_CONFIG

set(LLVM_CONFIG "llvm-config" CACHE PATH "Path to llvm-config executable")
find_program(LLVM_CONFIG_EXECUTABLE ${LLVM_CONFIG})
if(NOT LLVM_CONFIG_EXECUTABLE)
  message(FATAL_ERROR "llvm-config executable not found. Set LLVM_CONFIG to the path to llvm-config executable.")
endif()

execute_process(COMMAND ${LLVM_CONFIG} --ldflags OUTPUT_VARIABLE LLVM_LD_FLAGS)
execute_process(COMMAND ${LLVM_CONFIG} --cxxflags OUTPUT_VARIABLE LLVM_CXX_FLAGS)
execute_process(COMMAND ${LLVM_CONFIG} --includedir OUTPUT_VARIABLE LLVM_INCLUDE_FALGS)
string(REPLACE "\n" "" LLVM_INCLUDE_FALGS ${LLVM_INCLUDE_FALGS})
string(REPLACE "\n" "" LLVM_CXX_FLAGS ${LLVM_CXX_FLAGS})
string(REPLACE "\n" "" LLVM_LD_FLAGS ${LLVM_LD_FLAGS})

#set CXX flags
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${LLVM_LD_FLAGS}")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${LLVM_CXX_FLAGS} -I${LLVM_INCLUDE_FALGS}")
set(CMAKE_CXX_STANDARD 11)

target_link_libraries(Inv /usr/lib/llvm-17/lib/libLLVMCore.a)