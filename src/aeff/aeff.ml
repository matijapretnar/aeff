module Loader = Shared__Loader
module Runner = Shared__Runner
module Ast = Shared__Ast
module Error = Shared__Error

let make_top_step = function
  | Runner.TopOut (op, expr, proc) ->
      Format.printf "↑ %t %t@." (Ast.Operation.print op)
        (Ast.print_expression expr);
      proc
  | Runner.Step proc -> proc

let rec run (state : Loader.state) proc =
  match Runner.top_steps state.interpreter proc with
  | [] -> proc
  | steps ->
      let i = Random.int (List.length steps) in
      let _, top_step = List.nth steps i in
      let proc' = make_top_step top_step in
      run state proc'

let main () =
  match Array.to_list Sys.argv with
  | [] -> assert false
  | [ _aeff ] -> failwith ("Run AEff as '" ^ Sys.argv.(0) ^ " <filename>.aeff'")
  | _ :: filenames -> (
      try
        Random.self_init ();
        let state =
          List.fold_left Loader.load_file Loader.initial_state filenames
        in
        let proc = run state (Loader.make_process state) in
        Format.printf "The process has terminated in the configuration:@.%t@."
          (Ast.print_process proc)
      with Error.Error error ->
        Error.print error;
        exit 1 )

let _ = main ()