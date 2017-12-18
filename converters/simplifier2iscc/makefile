simplifier2iscc: *.cpp *.hpp makefile
	g++ ${LDFLAGS} -O3 -march=native -mtune=native -lginac -ldl -lcln -o $@ *.cpp

clean:
	\rm simplifier2iscc
