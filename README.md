# Hook

Install dependencies by

    opam install cow tiny_httpd

and build by running

    ocamlbuild -use-ocamlfind -pkgs cow,tiny_httpd hook.byte

Then, run

    ./hook.byte file1.hook file2.hook ...

This loads all the commands in all the listed files and starts a local HTTP server providing the interface.

