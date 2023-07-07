default: format
	dune build

format:
	dune build @fmt --auto-promote

release: format
	dune build --profile release

clean:
	dune clean

test:
	dune runtest

.PHONY: default format release clean test
