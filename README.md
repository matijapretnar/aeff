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

## Acknowledgements

<table>
      <tr><td>This project has received funding from the European Union’s Horizon 2020 research and innovation programme under the Marie Skłodowska-Curie grant agreement No 834146.</td><td><img src="https://danel.ahman.ee/images/eu_flag.jpg"></td></tr>
      <tr><td>This material is based upon work supported by the Air Force Office of Scientific Research under awards number FA9550-17-1-0326 and FA9550-21-1-0024.</td><td></td></tr>
</table>
