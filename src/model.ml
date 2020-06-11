type operation =
  | In of Ast.operation * Ast.expression
  | Out of Ast.operation * Ast.expression

type snapshot = {
    process: Ast.process;
    operations: operation list;
}

type loaded_code = {
    snapshot: snapshot;
    history: snapshot list;
    loader_state: Loader.state
}

type model = {
    loaded_code: loaded_code;
    unparsed_step_size: string;
    random_step_size: (int, string) result;
    unparsed_interrupt: string;
    parsed_interrupt: (Ast.operation * Ast.expression, string) result;
}

type msg =
  | Step of Runner.top_step
  | RandomStep
  | Interrupt
  | ParseInterrupt of string
  | ChangeStepSize of string
  | Back


let init loader_state proc = {
    loaded_code = {
        snapshot = {
            process = proc;
            operations = []
        };
        history = [];
        loader_state = loader_state;
    };
    unparsed_interrupt = "";
    unparsed_step_size = "1";
    random_step_size = Ok 1;
    parsed_interrupt = Error "enter \"op expr\""
}

let step_snapshot snapshot = function
  | Runner.Step proc' ->
        {snapshot with process = proc' }
  | Runner.TopOut (op, expr, proc') ->
        {process = proc'; operations = Out (op, expr) :: snapshot.operations}

let steps code =
    Runner.top_steps code.loader_state.interpreter code.snapshot.process

let move_to_snapshot code snapshot =
    {code with snapshot = snapshot; history = code.snapshot :: code.history}

let step_code code step = move_to_snapshot code (step_snapshot code.snapshot step)

let step_model model step = {model with loaded_code = step_code model.loaded_code step}

let interrupt code op expr =
    let proc' = Runner.incoming_operation code.snapshot.process op expr in
    move_to_snapshot code {process = proc'; operations = In (op, expr) :: code.snapshot.operations}

let rec make_random_steps code num_steps =
    match num_steps, steps code with
    | (0, _) | (_, []) -> code
    | _, steps ->
        let i = Random.int (List.length steps) in
        let (_, top_step) = List.nth steps i in
        let code' = step_code code top_step in
        make_random_steps code' (num_steps - 1)

let parse_step_size input =
    input
    |> int_of_string_opt
    |> Option.to_result ~none:(input ^ " is not an integer")

let parse_interrupt code input =
    try
        let lexbuf = Lexing.from_string input in
        let (op, term) = Parser.incoming_operation Lexer.token lexbuf in
        let op' = Desugarer.lookup_operation ~loc:term.Utils.at code.loader_state.desugarer op in
        let expr' = Desugarer.desugar_pure_expression code.loader_state.desugarer term in
        Ok (op', expr')
    with
        _ -> Error "error parsing stuff"

let update model = function
    | Step top_step ->
        step_model model top_step
    | RandomStep ->
        begin match model.random_step_size with
        | Ok num_steps -> {model with loaded_code = make_random_steps model.loaded_code num_steps}
        | Error _ -> model
        end
    | Back ->
        begin match model.loaded_code.history with
        | [] -> model
        | snapshot' :: history' -> {model with loaded_code = {model.loaded_code with snapshot = snapshot'; history = history'}}
        end
    | ChangeStepSize input ->
        let model = {model with unparsed_step_size = input} in
        {model with random_step_size = parse_step_size input}
    | ParseInterrupt input ->
        let model = {model with unparsed_interrupt = input} in
        {model with parsed_interrupt = parse_interrupt model.loaded_code input}
    | Interrupt ->
        begin match model.parsed_interrupt with
        | Ok (op, expr) -> {model with loaded_code = interrupt model.loaded_code op expr}
        | Error _ -> model
        end
