.PHONY: aeff.byte

default: aeff.byte

aeff.byte:
	ocamlbuild -use-ocamlfind -pkgs cow,tiny_httpd aeff.byte
