.PHONY: default release clean

default: format
	dune build

format:
	dune build @fmt --auto-promote

release: format
	dune build --profile release

clean:
	dune clean
