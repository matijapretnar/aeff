# Æff

Install dependencies by

    opam install menhir ocaml-vdom

and build by running (requires OCaml >= 4.08.0)

    dune build

Then, open `_build/default/src/aeff.html`, which provides a web interface that allows users to click through the asynchronous reductions of their programs.

For running the examples in `examples/`, also include the definitions from `pervasives.aeff`.
