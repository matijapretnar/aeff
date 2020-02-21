let parse_commands lexbuf =
    try Parser.commands Lexer.token lexbuf with
    | Parser.Error ->
        Error.syntax ~loc:(Location.of_lexeme (Lexing.lexeme_start_p lexbuf)) "parser error"
    | Failure failmsg when failmsg = "lexing: empty token" ->
        Error.syntax ~loc:(Location.of_lexeme (Lexing.lexeme_start_p lexbuf)) "unrecognised symbol."

type state = {
    desugarer : Desugarer.state;
    interpreter : Interpreter.state;
    top_computations : Ast.computation list
}

let initial_state () =
    let load_function state (x, def) =
        let desugarer_state', x' = Desugarer.add_external_variable x state.desugarer in
        let interpreter_state' = Interpreter.add_external_function x' def state.interpreter in
        {state with desugarer = desugarer_state'; interpreter = interpreter_state'}
    in
    {
        desugarer = Desugarer.initial_state;
        interpreter = Interpreter.initial_state;
        top_computations = []
    }
    |> fun state -> Utils.fold load_function state BuiltIn.functions


let execute_command state = function
| Ast.TyDef _ -> state
| Ast.TopLet (pat, comp) ->
    let interpreter_state' = Interpreter.eval_top_let state.interpreter pat comp in
    {state with interpreter = interpreter_state'}
| Ast.TopDo comp ->
    {state with top_computations = comp :: state.top_computations}
| Ast.Operation (x, op) ->
    let interpreter_state' = Interpreter.add_operation x op state.interpreter in
    {state with interpreter = interpreter_state'}

module S = Tiny_httpd

let redirect basepath url =
  S.Response.make_raw ~headers:[("Location", Format.sprintf "%s%s" basepath url)] ~code:302 ""

let print_request req = ()
   (* Format.printf "%t@." (fun ppf -> S.Request.pp_ ppf req) *)


let run_server state0 =
  let server = S.create () in
  let basepath = Format.sprintf "http://%s:%d" (S.addr server) (S.port server) in
  let state = ref [(state0.top_computations, [])] in
  let update_comps comps =
    let _, errors = List.nth !state 0 in
    state := (comps, errors) :: !state
  and add_msg msg =
    let comps, errors = List.nth !state 0 in
    print_endline msg;
    state := (comps, (View.Warning msg) :: errors) :: !state
  and both msg comps' =
    let _, errors = List.nth !state 0 in
    state := (comps', msg :: errors) :: !state
  in
  let view () =
    S.Response.make_string (Ok (View.show (List.nth !state 0)))
  in
  S.add_path_handler ~meth:`GET server
    "/" (fun req -> print_request req; view ());
  S.add_path_handler ~meth:`GET server
    "/step/%d/" (fun i req ->
        print_request req;
        try
            (match Runner.step_process state0.interpreter (List.nth !state 0 |> fst) i with
            | Some cs -> update_comps cs
            | None -> add_msg (Format.sprintf "Computation %d stuck." (i + 1)));
            redirect basepath "/"
        with
        | Error.Error (loc, error_kind, msg) ->
            S.Response.make (Error (500, msg))
    );
  S.add_path_handler ~meth:`GET server
    "/step/random/%d/" (fun num_steps req ->
        print_request req;
        try
            for step = 1 to num_steps do
                (match Runner.random_step state0.interpreter (List.nth !state 0 |> fst) with
                | Some cs -> update_comps cs
                | None -> add_msg "All computations stuck.")
            done;
            redirect basepath "/"
        with
        | Error.Error (loc, error_kind, msg) ->
            S.Response.make (Error (500, msg))
    );
  S.add_path_handler ~meth:`GET server
    "/back/" (fun req ->
        print_request req;
        try
            (match !state with
            | [] -> ()
            | [_] -> ()
            | _ :: old_state -> state := old_state);
            redirect basepath "/"
        with
        | Error.Error (loc, error_kind, msg) ->
            S.Response.make (Error (500, msg))
    );
  S.add_path_handler ~meth:`GET server
    "/operation/" (fun req ->
        print_request req;
        let params = S.Request.query req in
        try
            let input = List.assoc "operation" params in
            let lexbuf = Lexing.from_string input in
            let (op, term) = Parser.incoming_operation Lexer.token lexbuf in
            let op' = Desugarer.lookup_operation ~loc:term.Utils.at state0.desugarer op in
            let comp' = Desugarer.desugar_computation state0.desugarer term in
            both
                (View.Info (Format.sprintf "Incoming operation %s" input))
                (Runner.incoming_operation state0.interpreter (List.nth !state 0 |> fst) op' comp');
            redirect basepath "/"
        with
        | Error.Error (loc, error_kind, msg) ->
            S.Response.make (Error (500, msg))
    );
  Format.printf "listening on %s/@." basepath;
  S.run server

let main () =
    match Array.to_list Sys.argv with
    | [] ->
        assert false
    | [aeff] ->
        failwith ("Run AEff as '" ^ Sys.argv.(0) ^ " <filename>.aeff'")
    | _ :: filenames ->
        try
            let parse_file filename = Lexer.read_file parse_commands filename in
            let cmds = List.concat (List.map parse_file filenames) in
            let state = initial_state () in
            let desugarer_state', cmds' =
                Utils.fold_map Desugarer.desugar_command state.desugarer cmds
            in
            let state' = {state with desugarer=desugarer_state'} in
            let state'' = List.fold_left execute_command state' cmds'
            in
            run_server state''
        with
        | Error.Error error -> Error.print error; exit 1


let _ = main ()