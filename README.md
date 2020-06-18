# Æff

Install dependencies by

    opam install menhir ocaml-vdom

and build by running (requires OCaml >= 4.08.0)

    make

and you can clean up by running

    make clean

This gives you two options to run programs. The first option is a web interface,
accessible at `web/index.html`, which allows you to load one of the built-in
examples or enter your own program, and then interactively click through all its
(non-deterministic and asynchronous) reductions or introduce external interrupts.

The second option is a command line executable run as

    ./aeff.exe file1.aeff file2.aeff ...

which loads all the commands in all the listed files and starts evaluating the
given process, displaying all outgoing signals and the terminal configuration
(if there is one). Non-deterministic reductions are chosen randomly and there is
no option of introducing an external interrupt. For running the examples in
`examples/`, also include `stdlib.aeff` in the list of files to load.
