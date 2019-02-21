LIBS=-lLLVMCore -lLLVMBitReader -lLLVMSupport -lLLVMDemangle -lLLVMBinaryFormat -lncurses -lc++

CFLAGS  ?=-I$(HOME)/opt/llvm-7.0.1/include
LDFLAGS ?=-L$(HOME)/opt/llvm-7.0.1/lib
CLANG   ?=$(HOME)/opt/llvm-7.0.1/bin/clang

all : reader LLVMDis

reader : reader.bc
	$(CLANG) -o $@ $< $(LDFLAGS) $(LIBS)

reader.bc : reader.c
	$(CLANG) $(CFLAGS) -c -o $@ -emit-llvm $<

LLVMDis : LLVMDis.hs
	ghc LLVMDis.hs $(LDFLAGS) $(LIBS) -lc++

clean :
	rm -f reader.bc reader LLVMDis LLVMDis.o LLVMDis.hi

.PHONY : clean
