# Æff

Install dependencies by

    opam install menhir cow tiny_httpd

and build by running (requires OCaml >= 4.08.0)

    make

Then, run

    ./aeff.byte file1.aeff file2.aeff ...

This loads all the commands in all the listed files and starts a local HTTP server (at http://127.0.0.1:8080/) providing a web interface.

The web interface allows users to interactively click through the reductions of their asynchronous programs. 

For running the examples in `aeff/examples`, also include `pervasives.aeff` in the list of files to load.
