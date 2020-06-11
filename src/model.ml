type operation =
  | In of Ast.operation * Ast.expression
  | Out of Ast.operation * Ast.expression

type state = {
    process: Ast.process;
    operations: operation list;
}

type model = {
    state: state;
    history: state list;
    loader_state: Loader.state;
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
    state = {
        process = proc;
        operations = []
    };
    history = [];
    loader_state = loader_state;
    unparsed_interrupt = "";
    unparsed_step_size = "1";
    random_step_size = Ok 1;
    parsed_interrupt = Error "enter \"op expr\""
}

let step_state state = function
  | Runner.Step proc' ->
        {state with process = proc' }
  | Runner.TopOut (op, expr, proc') ->
        {process = proc'; operations = Out (op, expr) :: state.operations}

let steps model =
    Runner.top_steps model.loader_state.interpreter model.state.process

let move_to_state model state =
    {model with state = state; history = model.state :: model.history}

let step_model model step = move_to_state model (step_state model.state step)

let interrupt model op expr =
    let proc' = Runner.incoming_operation model.state.process op expr in
    move_to_state model {process = proc'; operations = In (op, expr) :: model.state.operations}

let rec make_random_steps model num_steps =
    match num_steps, steps model with
    | (0, _) | (_, []) -> model
    | _, steps ->
        let i = Random.int (List.length steps) in
        let (_, top_step) = List.nth steps i in
        let model' = step_model model top_step in
        make_random_steps model' (num_steps - 1)

let parse_step_size input =
    input
    |> int_of_string_opt
    |> Option.to_result ~none:(input ^ " is not an integer")

let parse_interrupt model input =
    try
        let lexbuf = Lexing.from_string input in
        let (op, term) = Parser.incoming_operation Lexer.token lexbuf in
        let op' = Desugarer.lookup_operation ~loc:term.Utils.at model.loader_state.desugarer op in
        let expr' = Desugarer.desugar_pure_expression model.loader_state.desugarer term in
        Ok (op', expr')
    with
        _ -> Error "error parsing stuff"

let update model = function
    | Step top_step ->
        step_model model top_step
    | RandomStep ->
        begin match model.random_step_size with
        | Ok num_steps -> make_random_steps model num_steps
        | Error _ -> model
        end
    | Back ->
        begin match model.history with
        | [] -> model
        | state' :: history' -> {model with state = state'; history = history'}
        end
    | ChangeStepSize input ->
        let model = {model with unparsed_step_size = input} in
        {model with random_step_size = parse_step_size input}
    | ParseInterrupt input ->
        let model = {model with unparsed_interrupt = input} in
        {model with parsed_interrupt = parse_interrupt model input}
    | Interrupt ->
        begin match model.parsed_interrupt with
        | Ok (op, expr) -> interrupt model op expr
        | Error _ -> model
        end
