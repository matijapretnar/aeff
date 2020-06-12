.PHONY: aeff.exe

default: aeff.exe

aeff.exe:
	dune build
	mkdir -p web
	ln -s ../_build/default/src/aeff.html web/aeff.html

clean:
	dune clean
	rm -rf web
