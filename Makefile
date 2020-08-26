all: zcc test clean

zcc:
	cargo build
	cp ./target/debug/zcc ./zcc 

test: zcc
	cargo test
	./test.sh

clean:
	rm -f zcc

.PHONY: test clean
