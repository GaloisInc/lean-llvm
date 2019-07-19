
LEAN_HOME=$(HOME)/opt/lean4
LLVM_HOME=$(HOME)/opt/llvm-8.0.0

LEAN:=$(LEAN_HOME)/bin/lean
LEANC:=$(LEAN_HOME)/bin/leanc
LEAN_INCLUDE:=$(LEAN_HOME)/include

LLVM_INCLUDE:=$(LLVM_HOME)/include
LLVM_BUILD_INCLUDE:=$(LLVM_HOME)/build/include

LLVM_LIB=$(LLVM_HOME)/build/lib

LLVM_LIBS := $(shell $(LLVM_HOME)/build/bin/llvm-config --libs)
CLANG_LIBS := -lclangAnalysis -lclangAST -lclangBasic -lclangCodeGen -lclangDriver -lclangEdit -lclangFrontend -lclangLex -lclangParse -lclangSema -lclangSerialization

CXX_FLAGS=-O1 -g -fno-rtti
CLANG=clang++

SOURCES :=\
  alignment.lean\
  ast.lean\
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

# make sure `build` exists
$(info $(shell mkdir -p build))

all : driver orc_test

tests/test_add.bc : tests/test_add.cpp
	$(LEANC) -o $@ -c -emit-llvm $<

tests/test_add.o : tests/test_add.cpp
	$(LEANC) -o $@ -c $<

tests/test_add.cpp : tests/test_add.lean
	$(LEAN) -c $@ $<

driver : $(OBJ) $(OLEAN) build/driver.o build/llvm_exports.o
	$(LEANC) -o $@ -L$(LLVM_LIB) $(LLVM_LIBS) -lz -ltermcap $(OBJ) build/driver.o build/llvm_exports.o

orc_test : build/orc_test.o build/llvm_ffi.o build/clang_ffi.o build/llvm_exports.o build/jit_exports.o
	$(LEANC) -o $@ -L$(LLVM_LIB) $(LLVM_LIBS) $(CLANG_LIBS) -lz -ltermcap $^

build/%.o : build/%.cpp
	$(LEANC) $(CXX_FLAGS) -o $@ -c -I$(LLVM_INCLUDE) -I$(LEAN_INCLUDE) $<

build/%.o : %.cpp
	$(LEANC) $(CXX_FLAGS) -o $@ -c -I$(LLVM_INCLUDE) -I$(LLVM_BUILD_INCLUDE) -I$(LEAN_INCLUDE) $<

build/%.cpp: %.lean %.olean
	$(LEAN) -c $@ $<

%.olean: %.lean
	$(LEAN) --make $<


build/llvm_exports.o : llvm_exports.h
build/jit_exports.o : llvm_exports.h

data_layout.olean : ast.olean parser.olean alignment.olean
driver.olean : ast.olean bv.olean pp.olean llvm_lib.olean simulate.olean
orc_test.olean : clang_ffi.olean llvm_ffi.olean
clang_ffi.olean : llvm_ffi.olean
llvm_lib.olean : ast.olean pp.olean parser.olean data_layout.olean llvm_ffi.olean
pp.olean : ast.olean
simulate.olean : ast.olean bv.olean pp.olean type_context.olean
type_context.olean : alignment.olean ast.olean data_layout.olean

clean:
	- rm -rf build llvm_exports.o
	- rm -f *.olean

.PHONY : clean all
.PRECIOUS : build/%.cpp build/%.o
