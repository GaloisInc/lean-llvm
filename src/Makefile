# This builds the lean-llvm.
#
# It assumes that lean and leanc are installed and that

LEAN_HOME=$(HOME)/code/lean4
LLVM_HOME?=$(HOME)/build/llvm-8.0.0.src/

#LEAN_HOME=$(HOME)/opt/lean4
#LLVM_HOME=$(HOME)/opt/llvm-8.0.0

# For now assume lean,leanc are in path
LEAN  := $(shell which lean)
LEANC := $(shell which leanc)

# We assume llvm-config is in path.
LLVM_CONFIG := llvm-config
LLVM_INCLUDE := $(shell $(LLVM_CONFIG) --includedir)
LLVM_LIB     := $(shell $(LLVM_CONFIG) --libdir)
LLVM_LIBS    := $(shell $(LLVM_CONFIG) --libs)

# Lean paths are computed relative to lean executable.
LEAN_HOME:=$(abspath $(dir $(LEAN))..)
LEAN_INCLUDE:=$(LEAN_HOME)/include
LEAN_LIBRARY:=$(LEAN_HOME)/lib/lean/library

CLANG_LIBS := -lclangAnalysis -lclangAST -lclangBasic -lclangCodeGen -lclangDriver -lclangEdit -lclangFrontend -lclangLex -lclangParse -lclangSema -lclangSerialization

CXX_FLAGS=-O1 -g -fno-rtti

SOURCES :=\
  alignment.lean\
  ast.lean\
  bv.lean\
  pp.lean\
  data_layout.lean\
  llvm_ffi.lean \
  llvm_lib.lean\
  memory.lean\
  sim_monad.lean\
  simulate.lean\
  parser.lean\
  type_context.lean\
  value.lean

LEAN_PATH:=$(PWD):$(LEAN_LIBRARY)

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
	$(LEANC) $(CXX_FLAGS) -o $@ -c -I$(LLVM_INCLUDE) -I$(LEAN_INCLUDE) $<

build/%.cpp: %.lean %.olean
	LEAN_PATH=$(LEAN_PATH) $(LEAN) -c $@ $<

%.olean: %.lean
	LEAN_PATH=$(LEAN_PATH) $(LEAN) --make $<


build/llvm_exports.o : llvm_exports.h
build/jit_exports.o : llvm_exports.h

data_layout.olean : ast.olean parser.olean alignment.olean
driver.olean : ast.olean bv.olean pp.olean llvm_lib.olean simulate.olean
orc_test.olean : clang_ffi.olean llvm_ffi.olean
clang_ffi.olean : llvm_ffi.olean
llvm_lib.olean : ast.olean pp.olean parser.olean data_layout.olean llvm_ffi.olean
memory.olean : ast.olean bv.olean pp.olean sim_monad.olean type_context.olean value.olean
sim_monad.olean : ast.olean bv.olean pp.olean type_context.olean value.olean
pp.olean : ast.olean
simulate.olean : ast.olean bv.olean memory.olean pp.olean sim_monad.olean type_context.olean value.olean
type_context.olean : alignment.olean ast.olean data_layout.olean
value.olean : ast.olean bv.olean type_context.olean 

clean:
	- rm -rf build llvm_exports.o
	- rm -f *.olean
	- rm -f tests/test_add.o

.PHONY : clean all
.PRECIOUS : build/%.cpp build/%.o
