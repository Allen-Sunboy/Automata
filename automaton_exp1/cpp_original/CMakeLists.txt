cmake_minimum_required(VERSION 3.8)
project(cpp)

set(CMAKE_CXX_STANDARD 17)

if(MINGW)
    add_link_options(-static -static-libgcc -static-libstdc++)
endif()
add_compile_options("$<$<C_COMPILER_ID:MSVC>:/utf-8>")
add_compile_options("$<$<CXX_COMPILER_ID:MSVC>:/utf-8>")

add_executable(nfa main-nfa.cpp nfa.cpp nfa.h)
