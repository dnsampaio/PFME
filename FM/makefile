CPP=clang++

#CPP=/home/undead/intel/bin/icpc
LINKEXTRA=-Wl,--no-as-needed

#Verbosity: Set variable |DEB_LVL| range: 0 - 11
#=====> Release <=========================
CXXEXTRA=-g0 -fmessage-length=0 -march=native -mtune=native -Wall -Wextra -pedantic -Werror -Ofast
VERBOSE=-DNDEBUG

#=====> Debug   <=========================
#CXXEXTRA=-g3 -O0 -fmessage-length=0 -Wall -Wextra -pedantic -Werror
#VERBOSE=-DDEB_LVL=6
#CXXEXTRA=-ggdb3
#======================================================================================================================================================
BASE=-std=c++11
CXXFLAGS=${BASE} -fPIC -pipe ${CXXEXTRA} ${VERBOSE}
LINK_FLAGS=${BASE} ${LDFLAGS} ${LINKEXTRA} -lglpk -lcln -lginac -ldl

#Simplifier rules
SRCS=Disjunction.cpp Conjunction.cpp Constraint.cpp debug.cpp main.cpp Schweighofer.cpp Simplifier.cpp
OBJS=$(SRCS:.cpp=.o) #Objects
IN=$(wildcard *.in)  #Inputs
OUT=$(IN:.in=.out)   #Outputs

#Simplifier parallel by bash script
SCR_OBJS=$(SRCS:.cpp=.scr.o) #Objects
SCR_IN=$(wildcard *.in)  #Inputs
SCR_OUT=$(IN:.in=.pout)  #Outputs

#SchweighoferTester (st) rules
SOBJS=$(SRCS:.cpp=.st.o) #Objects
SIN=$(wildcard *.sin)      #Inputs
SOUT=$(SIN:.sin=.sout)       #Outputs

#Interactive rules
IOBJS=$(SRCS:.cpp=.it.o) #Objects

#======================================================================================================================================================
#======================================================================================================================================================
all: Simplifier st simplify
run: $(OUT)
runST: $(SOUT)
runPR: $(SCR_OUT)

%.o: %.cpp makefile *.hpp
	${CPP} -c $(CXXFLAGS) -o $@ $<

%.st.o: %.cpp makefile *.hpp
	${CPP} -c -DDO_SCHWEIGHOFER_TESTER $(CXXFLAGS) -o $@ $<

%.scr.o: %.cpp makefile *.hpp
	${CPP} -c -DSCRIPT_CONTROL $(CXXFLAGS) -o $@ $<

%.it.o: %.cpp makefile *.hpp
	${CPP} -c -DINTERACTIVE_MODE $(CXXFLAGS) -o $@ $<

%.out: %.in Simplifier
	./Simplifier < $< > $@ 2>$(@:.out=.err)

%.sout: %.sin st
	./st < $< > $@ 2>$(@:.sout=.serr)

%.pout: %.in simplify ../Simplifier/Simplifier++.sh
		../Simplifier/Simplifier++.sh $<
		mv $<.all $@

Simplifier: $(OBJS)
	${CPP} ${LINK_FLAGS} ${CXXFLAGS} -o $@ $(OBJS)

st:$(SOBJS)
	${CPP} -DDO_SCHWEIGHOFER_TESTER ${LINK_FLAGS} ${CXXFLAGS} -o $@ $(SOBJS)

interactive: $(IOBJS)
	${CPP} -DINTERACTIVE_MODE ${LINK_FLAGS} ${CXXFLAGS} -o $@ $(IOBJS)

instrumented: $(SRCS) *.hpp
	clang++ -std=c++11 -g -fxray-instrument -lcln -lginac -ldl -w -O2 -DNDEBUG -o $@ $(SRCS)

simplify: $(SCR_OBJS)
	${CPP} ${LINK_FLAGS} ${CXXFLAGS} -o $@ $(SCR_OBJS)

clean:
	-rm -f Simplifier st interactive instrumented simplify *.o $(OUT) $(OUT:.out=.err) $(SOUT) $(SOUT:.sout=.serr)
