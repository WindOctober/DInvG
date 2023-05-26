cmake_minimum_required(VERSION 3.16.3)

option(USE_LSTINGX "Use the lstingx main function" OFF)
if(USE_LSTINGX)
    add_definitions(-DUSE_LSTINGX_MAIN)
endif()

project(PowerInv)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "${CMAKE_SOURCE_DIR}/bin")
set(CMAKE_EXPORT_COMPILE_COMMANDS ON CACHE INTERNAL "")
set(COPY_COMPILE_COMMANDS "${CMAKE_SOURCE_DIR}/compile_commands.json")
add_compile_options(-fexceptions)
add_executable(Inv ${CMAKE_SOURCE_DIR}/main.cpp)
set(EXECUTABLE_OUTPUT_PATH "${CMAKE_SOURCE_DIR}")
include_directories(${CMAKE_SOURCE_DIR})

file(MAKE_DIRECTORY "${CMAKE_SOURCE_DIR}/bin")


add_custom_command(
    OUTPUT ${COPY_COMPILE_COMMANDS}
    COMMAND ${CMAKE_COMMAND} -E copy_if_different
    ${CMAKE_BINARY_DIR}/compile_commands.json
    ${COPY_COMPILE_COMMANDS}
    DEPENDS ${CMAKE_BINARY_DIR}/compile_commands.json
    COMMENT "Copying compile_commands.json to project root directory"
)

foreach(target Inv) # 替换为您的项目名称或实际目标列表
    add_custom_command(TARGET ${target} POST_BUILD
        COMMAND ${CMAKE_COMMAND} -E copy_if_different
        ${CMAKE_BINARY_DIR}/compile_commands.json
        ${COPY_COMPILE_COMMANDS}
        COMMENT "Copying compile_commands.json to project root directory"
    )
endforeach()


#Adjust LLVM_CONFIG

set(LLVM_CONFIG "llvm-config-10" CACHE PATH "Path to llvm-config-10 executable")
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
  -lLLVM-10
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
set(LLVM_INCLUDE_FLAGS ${LLVM_INCLUDE_FLAGS} CACHE INTERNAL "LLVM include flags")
link_directories(${LLVM_LD_PATH})
include_directories(${LLVM_INCLUDE_FLAGS})
target_link_libraries(Inv ${CLANG_LIBS})

include_directories(${CMAKE_SOURCE_DIR}/Stingx)
add_subdirectory(Stingx)
target_link_libraries(Inv lstingx)

#set CXX flags
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS}  ${LLVM_LD_FLAGS}")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -I/usr/lib/gcc/x86_64-linux-gnu/9/include -fexceptions -DENABLE_LLVM_SHARED=1 ${LLVM_CXX_FLAGS}")

#Frontend commands

add_subdirectory(Frontend)
include_directories(${CMAKE_SOURCE_DIR}/Frontend)
target_link_libraries(Frontend lstingx)
target_link_libraries(Inv Frontend)

