(** Pretty-printing functions *)

let message ?loc ~header fmt =
  match loc with
  | Some loc ->
      Format.fprintf Format.err_formatter
        ("%s (%t):@," ^^ fmt ^^ "@.")
        header (Location.print loc)
  | _ -> Format.fprintf Format.err_formatter ("%s: " ^^ fmt ^^ "@.") header

let error ?loc err_kind fmt = message ?loc ~header:err_kind fmt

let check ?loc fmt = message ?loc ~header:"Check" fmt

let warning ?loc fmt = message ?loc ~header:"Warning" fmt

let debug ?loc fmt = message ?loc ~header:"Debug" fmt
