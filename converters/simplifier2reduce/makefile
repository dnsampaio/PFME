simplifier2reduce: *.cpp *.hpp makefile
	g++ ${LDFLAGS} -lginac -ldl -lcln -O3 -march=native -mtune=native -o $@ *.cpp

clean:
	\rm simplifier2reduce
