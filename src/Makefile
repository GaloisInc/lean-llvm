
LEAN_HOME=$(HOME)/opt/lean4
LLVM_HOME=$(HOME)/opt/llvm-8.0.0

LEAN:=$(LEAN_HOME)/bin/lean
LEANC:=$(LEAN_HOME)/bin/leanc
LEAN_INCLUDE:=$(LEAN_HOME)/include

LLVM_INCLUDE:=$(LLVM_HOME)/include
LLVM_LIB=$(LLVM_HOME)/lib

#LEAN_HOME=$(HOME)/code/lean4
#LLVM_HOME?=$(HOME)/build/llvm-8.0.0.src/

CLANG=clang++

SOURCES := ast.lean\
  bv.lean\
  driver.lean\
  pp.lean\
  data_layout.lean\
  llvm_ffi.lean \
  llvm_lib.lean\
  simulate.lean\
  parser.lean\
  type_context.lean

OLEAN=$(SOURCES:.lean=.olean)
CPP=$(patsubst %.lean,build/%.cpp,$(SOURCES))

all : driver

driver : $(CPP) $(OLEAN) llvm_exports.cpp
	$(LEANC) -O1 -g -L$(LLVM_LIB) -I$(LLVM_INCLUDE) -I$(LEAN_INCLUDE) -lLLVMCore -lLLVMSupport -lLLVMBinaryFormat -lLLVMDemangle -ltermcap -lLLVMBitReader -o "driver" llvm_exports.cpp $(CPP)

build/%.cpp: %.lean %.olean build
	$(LEAN) -c $@ $<

build :
	mkdir -p $@

%.olean: %.lean
	$(LEAN) --make $<

driver.olean : ast.olean bv.olean pp.olean llvm_lib.olean simulate.olean
llvm_lib.olean : ast.olean pp.olean parser.olean data_layout.olean llvm_ffi.olean
pp.olean : ast.olean
type_context.olean : ast.olean
data_layout.olean : ast.olean parser.olean
simulate.olean : ast.olean bv.olean pp.olean type_context.olean

clean:
	- rm -rf build
	- rm -f *.olean

.PHONY : clean all
