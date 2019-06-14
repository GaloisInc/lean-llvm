
LEAN_HOME=$(HOME)/code/lean4
LLVM_HOME=$(HOME)/build/llvm-8.0.0.src/
CLANG=clang++

SOURCES := ast.lean\
  bv.lean\
  pp.lean\
  simulate.lean\
  type_context.lean

OLEAN=$(SOURCES:.lean=.olean)
CPP=$(SOURCES:.lean=.cpp)
OBJS=$(SOURCES:.cpp=.o)

all : driver simple

driver : $(CPP) $(OLEAN) llvm_exports.cpp llvm_lib.cpp driver.cpp
	$(LEAN_HOME)/bin/leanc -O3 -g -L$(LLVM_HOME)/build/lib -I$(LLVM_HOME)/include -I$(LLVM_HOME)/build/include -I$(LEAN_HOME)/src -I$(LEAN_HOME)/src/runtime -lLLVMCore -lLLVMSupport -lLLVMBinaryFormat -lLLVMDemangle -ltermcap -lLLVMBitReader -o "driver" $(CPP) llvm_exports.cpp llvm_lib.cpp driver.cpp

simple:	$(CPP) $(OLEAN) simple.cpp
	$(LEAN_HOME)/bin/leanc -O3 -o "simple" simple.cpp $(CPP)

%.cpp:	%.lean %.olean
	$(LEAN_HOME)/bin/lean -c $@ $<

%.olean: %.lean
	$(LEAN_HOME)/bin/lean --make $<

clean:
	- rm $(CPP)
	- rm *.o
	- rm *.olean


.PHONY : clean all