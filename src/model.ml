type operation =
  | In of Ast.operation * Ast.expression
  | Out of Ast.operation * Ast.expression

type snapshot = { process : Ast.process; operations : operation list }

type loaded_code = {
  snapshot : snapshot;
  history : snapshot list;
  loader_state : Loader.state;
}

type model = {
  use_pervasives : bool;
  unparsed_code : string;
  loaded_code : (loaded_code, string) result;
  random_step_size : int;
  unparsed_interrupt : string;
  parsed_interrupt : (Ast.operation * Ast.expression, string) result;
}

type msg =
  | UsePervasives of bool
  | ChangeSource of string
  | LoadSource
  | Step of Runner.top_step
  | RandomStep
  | ChangeRandomStepSize of int
  | Interrupt
  | ParseInterrupt of string
  | Back

let init =
  {
    use_pervasives = true;
    unparsed_code = "";
    loaded_code = Error "";
    unparsed_interrupt = "";
    random_step_size = 1;
    parsed_interrupt = Error "";
  }

let step_snapshot snapshot = function
  | Runner.Step proc' -> { snapshot with process = proc' }
  | Runner.TopOut (op, expr, proc') ->
      { process = proc'; operations = Out (op, expr) :: snapshot.operations }

let apply_to_code_if_loaded f model =
  match model.loaded_code with
  | Ok code -> { model with loaded_code = Ok (f code) }
  | Error _ -> model

let steps code =
  Runner.top_steps code.loader_state.interpreter code.snapshot.process

let move_to_snapshot snapshot code =
  { code with snapshot; history = code.snapshot :: code.history }

let step_code step code =
  move_to_snapshot (step_snapshot code.snapshot step) code

let interrupt op expr code =
  let proc' = Runner.incoming_operation code.snapshot.process op expr in
  move_to_snapshot
    { process = proc'; operations = In (op, expr) :: code.snapshot.operations }
    code

let rec make_random_steps num_steps code =
  match (num_steps, steps code) with
  | 0, _ | _, [] -> code
  | _, steps ->
      let i = Random.int (List.length steps) in
      let _, top_step = List.nth steps i in
      let code' = step_code top_step code in
      make_random_steps (num_steps - 1) code'

let parse_step_size input =
  input |> int_of_string_opt
  |> Option.to_result ~none:(input ^ " is not an integer")

let parse_interrupt code input =
  try
    let lexbuf = Lexing.from_string input in
    let op, term = Parser.incoming_operation Lexer.token lexbuf in
    let op' =
      Desugarer.lookup_operation ~loc:term.Utils.at code.loader_state.desugarer
        op
    in
    let expr' =
      Desugarer.desugar_pure_expression code.loader_state.desugarer term
    in
    Ok (op', expr')
  with _ -> Error "error parsing stuff"

let parse_source source =
  let make_process = function
    | [] -> Ast.Run (Ast.Return (Ast.Tuple []))
    | comp :: comps ->
        List.fold_left
          (fun proc comp -> Ast.Parallel (proc, Ast.Run comp))
          (Ast.Run comp) comps
  in
  try
    let state = Loader.load_source source in
    let proc = make_process state.Loader.top_computations in
    Ok
      {
        snapshot = { process = proc; operations = [] };
        history = [];
        loader_state = state;
      }
  with Error.Error (_, _, msg) -> Error msg

let update model = function
  | UsePervasives use_pervasives -> { model with use_pervasives }
  | Step top_step -> apply_to_code_if_loaded (step_code top_step) model
  | RandomStep ->
      apply_to_code_if_loaded (make_random_steps model.random_step_size) model
  | Back -> (
      match model.loaded_code with
      | Ok ({ history = snapshot' :: history'; _ } as code) ->
          {
            model with
            loaded_code =
              Ok { code with snapshot = snapshot'; history = history' };
          }
      | _ -> model )
  | ChangeSource input -> { model with unparsed_code = input }
  | LoadSource ->
      {
        model with
        loaded_code =
          parse_source
            ( (if model.use_pervasives then Examples.pervasives else "")
            ^ "\n\n\n" ^ model.unparsed_code );
      }
  | ChangeRandomStepSize random_step_size -> { model with random_step_size }
  | ParseInterrupt input -> (
      match model.loaded_code with
      | Ok code ->
          let model = { model with unparsed_interrupt = input } in
          { model with parsed_interrupt = parse_interrupt code input }
      | Error _ -> model )
  | Interrupt -> (
      match model.parsed_interrupt with
      | Ok (op, expr) -> apply_to_code_if_loaded (interrupt op expr) model
      | Error _ -> model )
