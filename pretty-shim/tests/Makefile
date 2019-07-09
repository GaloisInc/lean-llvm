all : simple.ll simple.bc

simple.ll : simple.c
	clang -O1 -S -g -emit-llvm simple.c
simple.bc : simple.c
	clang -O1 -c -g -emit-llvm simple.c
