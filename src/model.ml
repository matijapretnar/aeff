type operation =
  | In of Ast.operation * Ast.expression
  | Out of Ast.operation * Ast.expression

type state = {
    process: Ast.process;
    steps: Runner.top_step list;
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
        steps = Runner.top_steps loader_state.Loader.interpreter proc;
        operations = []
    };
    history = [];
    loader_state = loader_state;
    unparsed_interrupt = "";
    unparsed_step_size = "1";
    random_step_size = Ok 1;
    parsed_interrupt = Error "enter \"op expr\""
}

let update_state interpreter_state state = function
  | Runner.Step proc' ->
        let steps' = Runner.top_steps interpreter_state proc' in
        {state with process = proc'; steps = steps' }
  | Runner.TopOut (op, expr, proc') ->
        let steps' = Runner.top_steps interpreter_state proc' in
        {process = proc'; steps = steps'; operations = Out (op, expr) :: state.operations}

let interrupt interpreter_state state op expr =
    let proc' = Runner.incoming_operation state.process op expr in
    let steps' = Runner.top_steps interpreter_state proc' in
    {process = proc'; steps = steps'; operations = In (op, expr) :: state.operations}

let rec make_random_steps interpreter_state state num_steps =
    match num_steps, state.steps with
    | (0, _) | (_, []) -> state
    | _ ->
        let i = Random.int (List.length state.steps) in
        let top_step = List.nth state.steps i in
        let state' = update_state interpreter_state state top_step in
        make_random_steps interpreter_state state' (num_steps - 1)

let update model = function
    | Step top_step ->
        let state' = update_state model.loader_state.interpreter model.state top_step in
        {model with state = state'; history = model.state :: model.history}
    | RandomStep ->
        begin match model.random_step_size with
        | Ok num_steps ->
            let state' = make_random_steps model.loader_state.interpreter model.state num_steps in
            {model with state = state'; history = model.state :: model.history}
        | Error _ -> model
        end
    | Back ->
        begin match model.history with
        | [] -> model
        | state' :: history' -> {model with state = state'; history = history'}
        end
    | ChangeStepSize input ->
        let model = {model with unparsed_step_size = input} in
        begin match int_of_string_opt input with
        | Some step_size ->
            {model with random_step_size = Ok step_size}
        | None ->
            {model with random_step_size = Error (input ^ " is not an integer")}
        end
    | ParseInterrupt input ->
        let model = {model with unparsed_interrupt = input} in
        begin try
            let lexbuf = Lexing.from_string input in
            let (op, term) = Parser.incoming_operation Lexer.token lexbuf in
            let op' = Desugarer.lookup_operation ~loc:term.Utils.at model.loader_state.desugarer op in
            let expr' = Desugarer.desugar_pure_expression model.loader_state.desugarer term in
            {model with parsed_interrupt = Ok (op', expr')}
        with
            _ -> {model with parsed_interrupt = Error "error parsing stuff"}
        end
    | Interrupt ->
        begin match model.parsed_interrupt with
        | Ok (op, expr) ->
            let state' = interrupt model.loader_state.interpreter model.state op expr in
            {model with state = state'; history = model.state :: model.history}
        | Error _ -> model
        end
