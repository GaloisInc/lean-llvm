#!/bin/bash
set -e

if [ -z ${LEAN_DIR+x} ] || [ -z ${LLVM_DIR+x} ]; then
    echo "Please set LEAN_DIR to lean root and LLVM_DIR to LLVM root"
    exit 1
fi

# Build C wrappers
clang++ "-I$LEAN_DIR/src" "-I$LEAN_DIR/src/runtime" -I$LLVM_DIR/include -std=c++11 -c llvm_exports.cpp

LEAN="$LEAN_DIR/bin/lean"
LEANC="$LEAN_DIR/bin/leanc"

$LEAN --cpp="dump_llvm.cpp" "dump_llvm.lean"

$LEANC -O3 -o "dump_llvm" "dump_llvm.cpp" llvm_exports.o -L$LLVM_DIR/lib -lLLVMCore -lLLVMSupport -lLLVMBinaryFormat -lLLVMDemangle -ltermcap -lLLVMBitReader -lLLVMSupport
