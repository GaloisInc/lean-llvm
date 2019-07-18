
LEAN_HOME=$(HOME)/opt/lean4
LLVM_HOME=$(HOME)/opt/llvm-8.0.0

LEAN:=$(LEAN_HOME)/bin/lean
LEANC:=$(LEAN_HOME)/bin/leanc
LEAN_INCLUDE:=$(LEAN_HOME)/include

LLVM_INCLUDE:=$(LLVM_HOME)/include
LLVM_BUILD_INCLUDE:=$(LLVM_HOME)/build/include

LLVM_LIB=$(LLVM_HOME)/build/lib

#LEAN_HOME=$(HOME)/code/lean4
#LLVM_HOME?=$(HOME)/build/llvm-8.0.0.src/

CLANG=clang++

SOURCES :=\
  alignment.lean\
  ast.lean\
  bv.lean\
  driver.lean\
  pp.lean\
  data_layout.lean\
  llvm_lib.lean\
  simulate.lean\
  parser.lean\
  type_context.lean

OLEAN=$(SOURCES:.lean=.olean)
CPP=$(SOURCES:.lean=.cpp)

all : driver

driver : $(CPP) $(OLEAN) llvm_exports.cpp driver.cpp
	$(LEANC) -O1 -g -L$(LLVM_LIB) -I$(LLVM_INCLUDE) -I$(LLVM_BUILD_INCLUDE) -I$(LEAN_INCLUDE) -lLLVMCore -lLLVMSupport -lLLVMBinaryFormat -lLLVMDemangle -ltermcap -lLLVMBitReader -o "driver" llvm_exports.cpp $(CPP)

%.cpp:	%.lean %.olean
	$(LEAN) -c $@ $<

%.olean: %.lean
	$(LEAN) --make $<


data_layout.olean : ast.olean parser.olean alignment.olean
driver.olean : ast.olean bv.olean pp.olean llvm_lib.olean simulate.olean
llvm_lib.olean : ast.olean pp.olean parser.olean data_layout.olean
pp.olean : ast.olean
simulate.olean : ast.olean bv.olean pp.olean type_context.olean
type_context.olean : alignment.olean ast.olean data_layout.olean


clean:
	- rm -f $(CPP)
	- rm -f *.olean


.PHONY : clean all
