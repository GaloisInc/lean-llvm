cmake_minimum_required(VERSION 3.4.3)
project (jit_test)

# Find clang and LLVM
find_package(CLANG REQUIRED CONFIG)
# Once clang is no longer needed, we can replace this with:
#   find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found CLANG ${CLANG_PACKAGE_VERSION}")
message(STATUS "Using ClangConfig.cmake in: ${CLANG_DIR}")
message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

include_directories(${LLVM_INCLUDE_DIRS})
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-rtti -std=c++14")

add_executable(jit_test jit_test.cpp)

# Find the libraries that correspond to the LLVM components
# that we wish to use
llvm_map_components_to_libnames(llvm_libs orcjit x86codegen)

set(clang_libs clangCodeGen)

# Link against LLVM libraries
target_link_libraries(jit_test ${llvm_libs} ${clang_libs})
