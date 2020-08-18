all: test clean

zcc:
	cargo build
	cp ./target/debug/zcc ./zcc 

test: zcc
	./test.sh

clean:
	rm -f zcc tmp*

.PHONY: test clean
