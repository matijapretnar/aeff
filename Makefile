.PHONY: aeff.exe

default: aeff.exe

aeff.exe:
	dune build src

clean:
	dune clean
