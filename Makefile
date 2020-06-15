.PHONY: default release clean

default:
	dune build

release:
	dune build --profile release

clean:
	dune clean
