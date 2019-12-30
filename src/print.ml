(** Pretty-printing functions *)

let message ~verbosity ?loc ~header fmt =
    match loc with
    | Some loc ->
        Format.fprintf Format.err_formatter
          ("%s (%t):@," ^^ fmt ^^ "@.")
          header (Location.print loc)
    | _ ->
        Format.fprintf Format.err_formatter ("%s: " ^^ fmt ^^ "@.") header

let error ?loc err_kind fmt = message ~verbosity:1 ?loc ~header:err_kind fmt

let check ?loc fmt = message ~verbosity:2 ?loc ~header:"Check" fmt

let warning ?loc fmt = message ~verbosity:3 ?loc ~header:"Warning" fmt

let debug ?loc fmt = message ~verbosity:4 ?loc ~header:"Debug" fmt
