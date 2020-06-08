.PHONY: aeff.exe

default: aeff.exe

aeff.exe:
	dune build src/aeff.exe

clean:
	dune clean
