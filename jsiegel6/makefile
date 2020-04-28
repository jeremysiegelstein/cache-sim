all: cache-sim

cache-sim:	main.o
	g++ main.o -o cache-sim

main.o: main.cpp
	g++ -Wall -Wextra -pedantic -std=c++17 -c main.cpp

clean:
	-rm -f *.o cache-sim
