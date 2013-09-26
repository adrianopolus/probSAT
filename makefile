CC=gcc
CFLAGS= -Wall -Wextra -static -O3 -funroll-loops -fexpensive-optimizations 
#CFLAGS=  -pg -ggdb -Wall -lm   -Wno-missing-braces -static 

all: probSAT

probSATsc13:	probSAT.c
			$(CC) $(CFLAGS)  probSAT.c -lm -o probSAT
clean:	
		rm -f probSAT

