# Æff

Install dependencies by

    opam install menhir cow tiny_httpd

and build by running

    ocamlbuild -use-ocamlfind -pkgs cow,tiny_httpd aeff.byte

Then, run

    ./aeff.byte file1.aeff file2.aeff ...

This loads all the commands in all the listed files and starts a local HTTP server providing the interface.

