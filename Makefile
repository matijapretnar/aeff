default: format
	dune build

format:
	dune build @fmt --auto-promote

release: format
	dune build --profile release

clean:
	dune clean

generate_tests: 
	dune build @generate_tests --auto-promote

test: generate_tests
	dune runtest

.PHONY: default format release clean generate_tests test
