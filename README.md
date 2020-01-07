# Hook

Run `ocamlbuild hook.byte` and then run `hook.byte file1.hook file2.hook ...`. This loads all the commands in all the listed files and starts executing them one by one.

You run computations by `do ...`. This goes through evaluation steps one by one and asks you at each step whether to trigger an incoming operation, which you do by writing `op arg`.
