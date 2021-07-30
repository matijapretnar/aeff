open Utils
module Ast = Core.Ast
module Interpreter = Core.Interpreter
module Loader = Core.Loader

let make_top_step = function
  | Interpreter.TopSignal (op, expr, proc) ->
      Format.printf "↑ %t %t@." (Ast.OpSym.print op)
        (Ast.print_expression expr);
      proc
  | Interpreter.Step proc -> proc

let rec run (state : Interpreter.state) proc =
  match Interpreter.top_steps state proc with
  | [] -> proc
  | steps ->
      let i = Random.int (List.length steps) in
      let _, top_step = List.nth steps i in
      let proc' = make_top_step top_step in
      run state proc'

type config = {
  filenames : string list;
  load_stdlib : bool;
  fixed_random_seed : bool;
}

let parse_args_to_config () =
  let filenames = ref []
  and load_stdlib = ref true
  and fixed_random_seed = ref false in
  let usage = "Run AEff as '" ^ Sys.argv.(0) ^ " [filename.aeff] ...'"
  and anonymous filename = filenames := filename :: !filenames
  and options =
    Arg.align
      [
        ( "--no-stdlib",
          Arg.Clear load_stdlib,
          " Do not load the standard library" );
        ( "--fixed-random-seed",
          Arg.Set fixed_random_seed,
          " Do not initialize the random seed" );
      ]
  in
  Arg.parse options anonymous usage;
  {
    filenames = List.rev !filenames;
    load_stdlib = !load_stdlib;
    fixed_random_seed = !fixed_random_seed;
  }

let main () =
  let config = parse_args_to_config () in
  try
    if not config.fixed_random_seed then Random.self_init ();
    let state =
      if config.load_stdlib then
        Loader.load_source Loader.initial_state Loader.stdlib_source
      else Loader.initial_state
    in
    let state = List.fold_left Loader.load_file state config.filenames in
    let proc = run state.interpreter (Loader.make_process state) in
    Format.printf "The process has terminated in the configuration:@.%t@."
      (Ast.print_process proc)
  with Error.Error error ->
    Error.print error;
    exit 1

let _ = main ()
