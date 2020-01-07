let parse_commands lexbuf =
    try Parser.commands Lexer.token lexbuf with
    | Parser.Error ->
        Error.syntax ~loc:(Location.of_lexeme (Lexing.lexeme_start_p lexbuf)) "parser error"
    | Failure failmsg when failmsg = "lexing: empty token" ->
        Error.syntax ~loc:(Location.of_lexeme (Lexing.lexeme_start_p lexbuf)) "unrecognised symbol."

let rec incoming_operation () =
    let str = print_string "OP? "; read_line () in
    let lexbuf = Lexing.from_string str in
    try Parser.incoming_operation Lexer.token lexbuf with
    | Parser.Error ->
        (Print.warning ~loc:(Location.of_lexeme (Lexing.lexeme_start_p lexbuf)) "parser error";
        incoming_operation ())
    | Failure failmsg when failmsg = "lexing: empty token" ->
        (Print.warning ~loc:(Location.of_lexeme (Lexing.lexeme_start_p lexbuf)) "parser error";
        incoming_operation ())


type state = {
    desugarer : Desugarer.state;
    interpreter : Interpreter.state;
}

let initial_state () =
    let load_function state (x, def) =
        let desugarer_state', x' = Desugarer.add_external_variable x state.desugarer in
        let interpreter_state' = Interpreter.add_external_function x' def state.interpreter in
        {desugarer = desugarer_state'; interpreter = interpreter_state'}
    in
    {
        desugarer = Desugarer.initial_state;
        interpreter = Interpreter.initial_state;
    }
    |> fun state -> Utils.fold load_function state BuiltIn.functions

let rec run state comp =
    Format.printf "%t@." (Ast.print_computation comp);
    try
        match comp with
        | Ast.Return expr ->
            Format.printf "FINAL VALUE: %t@." (Ast.print_expression expr)
        | Ast.Out (op, expr, comp) ->
            Format.printf "  ~~[↑%t %t]~~>@." (Ast.Operation.print op) (Ast.print_expression expr);
            run state (Interpreter.step state.interpreter comp)
        | comp ->
            begin match incoming_operation () with
            | Some (op, term) ->
                let op' = Desugarer.lookup_operation ~loc:term.at state.desugarer op in
                let comp' = Desugarer.desugar_computation state.desugarer term in
                let expr = Interpreter.eval_expr state.interpreter comp' in
                Format.printf "  ~~[↓%t %t]~~>@." (Ast.Operation.print op') (Ast.print_expression expr);
                run state (Ast.In (op', expr, comp))
            | None ->
                Format.printf "  ~~>@.";
                run state (Interpreter.step state.interpreter comp)
            end
    with
        Interpreter.Stuck ->
            Format.printf "STUCK! @.";
            run state comp


let execute_command state = function
| Ast.TyDef _ -> state
| Ast.TopLet (pat, comp) ->
    let interpreter_state' = Interpreter.eval_top_let state.interpreter pat comp in
    Format.printf "val %t@." (Ast.print_pattern pat);
    {state with interpreter = interpreter_state'}
| Ast.TopDo comp ->
    run state comp;
    state
| Ast.Operation (x, op) ->
    let interpreter_state' = Interpreter.add_operation x op state.interpreter in
    Format.printf "operation %t@." (Ast.Operation.print op);
    {state with interpreter = interpreter_state'}

let main () =
    match Array.to_list Sys.argv with
    | [] ->
        assert false
    | [hook] ->
        failwith ("Run HOOK as '" ^ Sys.argv.(0) ^ " <filename>.hook'")
    | _ :: filenames ->
        try
            let parse_file filename = Lexer.read_file parse_commands filename in
            let cmds = List.concat (List.map parse_file filenames) in
            let state = initial_state () in
            let desugarer_state', cmds' =
                Utils.fold_map Desugarer.desugar_command state.desugarer cmds
            in
            let state' = {state with desugarer=desugarer_state'} in
            let _ = List.fold_left execute_command state' cmds'
            in
            ()
        with
        | Error.Error error -> Error.print error; exit 1

let _ = main ()
