open Core

type operation =
  | In of Ast.operation * Ast.expression
  | Out of Ast.operation * Ast.expression

type snapshot = { process : Ast.process; operations : operation list }

type loaded_code = {
  snapshot : snapshot;
  history : snapshot list;
  interpreter_state : Interpreter.state;
  operations : Ast.ty Ast.OperationMap.t;
  parse_payload : Ast.operation -> string -> Ast.expression;
}

type model = {
  use_stdlib : bool;
  unparsed_code : string;
  loaded_code : (loaded_code, string) result;
  selected_reduction : int option;
  random_step_size : int;
  interrupt_operation : Ast.operation option;
  unparsed_interrupt_payload : string;
  parsed_interrupt_payload : (Ast.expression, string) result;
}

type msg =
  | UseStdlib of bool
  | ChangeSource of string
  | LoadSource
  | SelectReduction of int option
  | Step of Runner.top_step
  | RandomStep
  | ChangeRandomStepSize of int
  | ChangeInterruptOperation of Ast.operation
  | ParseInterruptPayload of string
  | Interrupt
  | Back

let init =
  {
    use_stdlib = true;
    unparsed_code = "";
    loaded_code = Error "";
    selected_reduction = None;
    random_step_size = 1;
    interrupt_operation = None;
    unparsed_interrupt_payload = "";
    parsed_interrupt_payload = Error "";
  }

let step_snapshot snapshot = function
  | Runner.Step proc' -> { snapshot with process = proc' }
  | Runner.TopOut (op, expr, proc') ->
      { process = proc'; operations = Out (op, expr) :: snapshot.operations }

let apply_to_code_if_loaded f model =
  match model.loaded_code with
  | Ok code -> { model with loaded_code = Ok (f code) }
  | Error _ -> model

let steps code = Runner.top_steps code.interpreter_state code.snapshot.process

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

let parse_payload code op input =
  try Ok (code.parse_payload op input) with
  | Utils.Error.Error (_, kind, msg) -> Error (kind ^ ": " ^ msg)
  | _ -> Error "Parser error"

let parse_source source =
  try
    let state = Loader.load_source Loader.initial_state source in
    let proc = Loader.make_process state in
    Ok
      {
        snapshot = { process = proc; operations = [] };
        history = [];
        interpreter_state = state.interpreter;
        parse_payload = Loader.parse_payload state;
        operations = state.typechecker.operations;
      }
  with Utils.Error.Error (_, _, msg) -> Error msg

let update model = function
  | UseStdlib use_stdlib -> { model with use_stdlib }
  | SelectReduction selected_reduction -> { model with selected_reduction }
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
            ( (if model.use_stdlib then Examples.stdlib else "")
            ^ "\n\n\n" ^ model.unparsed_code );
      }
  | ChangeRandomStepSize random_step_size -> { model with random_step_size }
  | ChangeInterruptOperation operation ->
      { model with interrupt_operation = Some operation }
  | ParseInterruptPayload input -> (
      match (model.interrupt_operation, model.loaded_code) with
      | Some op, Ok code ->
          let model = { model with unparsed_interrupt_payload = input } in
          { model with parsed_interrupt_payload = parse_payload code op input }
      | _, _ -> model )
  | Interrupt -> (
      match (model.interrupt_operation, model.parsed_interrupt_payload) with
      | Some op, Ok expr -> apply_to_code_if_loaded (interrupt op expr) model
      | _, _ -> model )
