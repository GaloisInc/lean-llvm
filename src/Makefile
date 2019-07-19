
LEAN_HOME=$(HOME)/opt/lean4
LLVM_HOME=$(HOME)/opt/llvm-8.0.0

LEAN:=$(LEAN_HOME)/bin/lean
LEANC:=$(LEAN_HOME)/bin/leanc
LEAN_INCLUDE:=$(LEAN_HOME)/include

LLVM_INCLUDE:=$(LLVM_HOME)/include
LLVM_LIB=$(LLVM_HOME)/lib

LLVM_LIBS := $(shell llvm-config --libs)
CLANG_LIBS := -lclangAnalysis -lclangAST -lclangBasic -lclangCodeGen -lclangDriver -lclangEdit -lclangFrontend -lclangLex -lclangParse -lclangSema -lclangSerialization

CXX_FLAGS=-O1 -g

#LEAN_HOME=$(HOME)/code/lean4
#LLVM_HOME?=$(HOME)/build/llvm-8.0.0.src/

CLANG=clang++

SOURCES := ast.lean\
  bv.lean\
  pp.lean\
  data_layout.lean\
  llvm_ffi.lean \
  llvm_lib.lean\
  simulate.lean\
  parser.lean\
  type_context.lean

OLEAN=$(SOURCES:.lean=.olean)
CPP=$(patsubst %.lean,build/%.cpp,$(SOURCES))
OBJ=$(patsubst %.lean,build/%.o,$(SOURCES))

all : driver orc_test

tests/test_add.bc : tests/test_add.cpp
	$(LEANC) -o $@ -c -emit-llvm $<

tests/test_add.o : tests/test_add.cpp
	$(LEANC) -o $@ -c $<

tests/test_add.cpp : tests/test_add.lean
	$(LEAN) -c $@ $<

build/llvm_exports.o : llvm_exports.h


build/%.o : %.cpp
	$(LEANC) $(CXX_FLAGS) -g -o $@ -c -I$(LLVM_INCLUDE) -I$(LEAN_INCLUDE) $<

build/llvm_exports.o : llvm_exports.h
build/jit_exports.o : llvm_exports.h

driver : $(OBJ) $(OLEAN) build/driver.o build/llvm_exports.o
	$(LEANC) -o $@ -L$(LLVM_LIB) $(LLVM_LIBS) $(CLANG_LIBS) -lz -ltermcap $(OBJ) build/driver.o build/llvm_exports.o

orc_test : build/orc_test.o build/llvm_ffi.o build/llvm_exports.o build/jit_exports.o
	$(LEANC) -o $@ -L$(LLVM_LIB) $(LLVM_LIBS) $(CLANG_LIBS) -lz -ltermcap $^


build :
	mkdir -p $@

build/%.cpp: %.lean build
	$(LEAN) -c $@ $<

.PRECIOUS : build/%.cpp

build/%.o : build/%.cpp
	$(LEANC) $(CXX_FLAGS) -o $@ -c -I$(LLVM_INCLUDE) -I$(LEAN_INCLUDE) $<

%.olean: %.lean
	$(LEAN) --make $<

ast.cpp : ast.lean

build/orc_test.cpp : llvm_ffi.olean

driver.olean : ast.olean bv.olean pp.olean llvm_lib.olean simulate.olean
llvm_lib.olean : ast.olean pp.olean parser.olean data_layout.olean llvm_ffi.olean
pp.olean : ast.olean
type_context.olean : ast.olean
data_layout.olean : ast.olean parser.olean
simulate.olean : ast.olean bv.olean pp.olean type_context.olean

clean:
	- rm -rf build llvm_exports.o
	- rm -f *.olean

%.o : %.cpp


.PHONY : clean all
