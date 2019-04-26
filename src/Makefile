
LEAN_HOME=$(HOME)/code/lean4

SOURCES := ast.lean\
  pp.lean\
  type_context.lean\
  simple.lean

OLEAN=$(SOURCES:.lean=.olean)
CPP=$(SOURCES:.lean=.cpp)
OBJS=$(SOURCES:.cpp=.o)

simple:	$(CPP) $(OLEAN)
	clang++ -std=c++14 -D LEAN_MULTI_THREAD -pthread -fPIC -I$(LEAN_HOME)/src -L$(LEAN_HOME)/build/release -L$(LEAN_HOME)/build/release/stage1 -ldl -lleanstatic -lleanstdlib -lgmp -o $@ $(CPP)

%.cpp:	%.lean %.olean
	lean -c $@ $<

%.olean: %.lean
	lean --make $<

clean:
	- rm *.cpp
	- rm *.o
	- rm *.olean


.PHONY : clean
