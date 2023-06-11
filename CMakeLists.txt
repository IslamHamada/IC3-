cmake_minimum_required(VERSION 3.25)
project(IC3+)

set(CMAKE_CXX_STANDARD 17)

set(CMAKE_BUILD_TYPE Release)
#set(CMAKE_BUILD_TYPE Debug)

#set(CMAKE_CXX_FLAGS "-Wall -Wextra")
#set(CMAKE_CXX_FLAGS_DEBUG "-g")
#set(CMAKE_CXX_FLAGS_RELEASE "-O3")

add_executable(IC3+ main.cpp Model.cpp IC3.cpp
        ./minisat/minisat/core/Solver.cc
        ./minisat/minisat/simp/SimpSolver.cc
        ./minisat/minisat/utils/System.cc
        ./aiger/aiger.c IC3.cpp Model.cpp)
