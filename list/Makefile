CPPC=clang++
CPPFLAGS=-std=c++20 -Wall

INCLUDES=-I../../Trieste/include -I../../Trieste/mac_build/_deps/cli11-src/include

SRC=parse.cc lang.cc
OBJ=$(SRC:.cc=.o)

all: main

%.o: %.cc lang.hh wf.hh
	$(CPPC) -c $(CPPFLAGS) $(INCLUDES) $<

main: $(OBJ) main.cc
	$(CPPC) $(CPPFLAGS) $(INCLUDES) $^ -o main

run: main
	./main build -w programs/test.list

.PHONY: all run