CFLAGS=-std=c11 -g -static -fno-common
all: clean zcc test check

zcc: clean
	cargo build
	cp ./target/debug/zcc ./zcc 

test: zcc
	cargo test -- --nocapture
	./zcc tests/tests.c > tmp.s
	$(CC) -static -o tmp tmp.s
	./tmp

check:
	cargo fmt --all -- --check

clean:
	rm -f zcc tmp*

.PHONY: test clean check
