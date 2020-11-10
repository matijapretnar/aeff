# Æff

Install dependencies by

    opam install menhir ocaml-vdom ocamlformat

and build Æff by running (requires OCaml >= 4.08.0)

    make

and you can clean up by running

    make clean

Æff gives you two options to run programs: 

- The first option is a web interface,
  accessible at `web/index.html`, which allows you to load one of the built-in
  examples or enter your own program, and then interactively click through all its
  (non-deterministic and asynchronous) reductions or introduce external interrupts.

- The second option is a command line executable run as

      ./aeff.exe file1.aeff file2.aeff ...

  which loads all the commands in all the listed files and starts evaluating the
  given program, displaying all outgoing signals and the terminal configuration
  (if there is one). Non-deterministic reductions are chosen randomly and there is
  no option of introducing external interrupts. If you do not want to load the
  standard library, run Æff with the `--no-stdlib` option.
