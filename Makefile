all: gen
	$(MAKE) -C gentest all

test: gen
	$(MAKE) -C gentest test

gen:
	cargo build
	target/modp > gentest/src/gen.rs
