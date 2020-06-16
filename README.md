# Æff

Install dependencies by

    opam install menhir ocaml-vdom

and build by running (requires OCaml >= 4.08.0)

    make

and you can clean up by running

    make clean

Then, open `web/index.html`, which links to a web interface that allows you to enter your program,
and then click through (all the non-deterministic and asynchronous) reductions of it.

For running the examples in `examples/`, you also need to prepend the definitions from `pervasives.aeff` into the web interface.
