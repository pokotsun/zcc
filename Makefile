CFLAGS=-std=c11 -g -static -fno-common

all: test clean

zcc: main.o
	$(CC) -o zcc main.o $(LDFLAGS)

test: zcc
	./test.sh

clean:
	rm -f zcc *.o *~ tmp*

.PHONY: test clean
