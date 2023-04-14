include Makefile.globals
## please leave this alone.
LOCALINCS = -I .

## sources.
## you should not need to edit beyond this line
SRC_NAME=  Clump \
           Context \
           DisequalityStore \
           DualInvariantMap \
           DualTransitionRelation \
           Expression \
           ExpressionStore \
           funcs \
           InvariantMap \
           LinExpr \
           LinTransform \
           Location \
           MatrixStore \
           PolyStore \
           PolyUtils \
           Rational \
           SparseLinExpr \
           SparseLinTransform \
           System \
           Timer \
           TransitionRelation \
           var-info \
           Elimination \
           Tree \
           ToolUtils \
           Propagation \
           Macro



HDRS = $(addsuffix .h, $(SRC_NAME)) myassertions.h global_types.h

OBJFILES= $(addsuffix .o, $(SRC_NAME)) ltrtest.tab.o lex.yy.o

SRC= $(addsuffix .cc, $(SRC_NAME)) ltrtest.tab.c lex.yy.c


LIBS = -lppl -lgmpxx -lgmp 

CC= g++


CCFLAGS = -g -Wall -Wno-deprecated

OBJFLAGS = -c -g -Wall -Wno-deprecated


.PHONY: clean depend 
.SUFFIXES: .cc .h .o .c
.PRECIOUS: $(SRC)  $(HDRS)


all: depend lstingx

lstingx: $(OBJFILES)  
	$(CC) $(CCFLAGS) $(GLBINCS)  $(LOCALINCS) $(GLBLIBS) \
	 -o lstingx $(OBJFILES) $(LIBS)

%.tab.c: %.y
	$(BISON) -y -d -o $*.tab.c $*.y


lex.yy.c: ltrtest.l
	flex -l ltrtest.l

%.o: %.c
	$(CC) $(OBJFLAGS)  $(GLBINCS) $(LOCALINCS) $*.c -o $*.o
%.o:%.cc 
	$(CC) $(OBJFLAGS) $(GLBINCS) $(LOCALINCS) $*.cc -o $*.o

depend: $(SRC)
	makedepend -Y $(LOCALINCS) $(GLBINCS) -fMakefile.deps $(SRC) 2> /dev/null
clean:
	rm $(OBJFILES) lstingx  \
	 lex.yy.c  ltrtest.tab.c ltrtest.tab.h

include Makefile.deps
