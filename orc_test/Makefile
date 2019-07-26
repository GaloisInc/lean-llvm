LLVM_HOME:=$(HOME)/opt/llvm-8.0.0
LLVM_INCLUDE:=$(LLVM_HOME)/include
LLVM_LIBDIR :=$(LLVM_HOME)/lib

# LLVM_LIBS := $(shell llvm-config --libs orcjit x86codegen)
LLVM_LIBS := $(shell llvm-config --libs)
CLANG_LIBS := -lclangAnalysis -lclangAST -lclangBasic -lclangCodeGen -lclangDriver -lclangEdit -lclangFrontend -lclangLex -lclangParse -lclangSema -lclangSerialization

all : jit_test

fib.bc : fib.c
	clang -c -emit-llvm $<

% : %.cpp

% : %.o
	clang++ -std=c++14 -o $@ -O3 -L$(LLVM_LIBDIR) $(CLANG_LIBS) $(LLVM_LIBS) -lz -ltermcap $<

%.o : %.cpp
	clang++ -Wall -std=c++14 -g -o $@ -I$(LLVM_INCLUDE) -fno-rtti -g -c $<

clean :
	rm -rf ll main ll.o main.o

.PRECIOUS : %.o

.PHONY : all clean
