all: zcc test

zcc: clean
	cargo build
	cp ./target/debug/zcc ./zcc 

test: zcc
	cargo test -- --nocapture
	./test.sh

clean:
	rm -f zcc tmp*

.PHONY: test clean
