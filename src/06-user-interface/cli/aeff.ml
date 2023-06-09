open Utils
module Ast = Language.Ast
module Backend = CliInterpreter
module Loader = Loader.Loader (Backend)

type config = {
  filenames : string list;
  use_stdlib : bool;
  fixed_random_seed : bool;
}

let parse_args_to_config () =
  let filenames = ref []
  and use_stdlib = ref true
  and fixed_random_seed = ref false in

  let usage = "Run AEff as '" ^ Sys.argv.(0) ^ " [filename.aeff] ...'"
  and anonymous filename = filenames := filename :: !filenames
  and options =
    Arg.align
      [
        ( "--no-stdlib",
          Arg.Clear use_stdlib,
          " Do not load the standard library" );
        ( "--fixed-random-seed",
          Arg.Set fixed_random_seed,
          " Do not initialize the random seed" );
      ]
  in
  Arg.parse options anonymous usage;
  {
    filenames = List.rev !filenames;
    use_stdlib = !use_stdlib;
    fixed_random_seed = !fixed_random_seed;
  }

let rec run (state : Backend.run_state) =
  Backend.view_run_state state;
  match Backend.steps state with
  | [] -> ()
  | steps ->
      let i = Random.int (List.length steps) in
      let step = List.nth steps i in
      let state' = step.next_state () in
      run state'

let main () =
  let config = parse_args_to_config () in
  try
    Random.self_init ();
    let state =
      if config.use_stdlib then
        Loader.load_source Loader.initial_state Loader.stdlib_source
      else Loader.initial_state
    in
    let state' = List.fold_left Loader.load_file state config.filenames in
    let run_state = Backend.run state'.backend in
    run run_state
  with Error.Error error ->
    Error.print error;
    exit 1

let _ = main ()
