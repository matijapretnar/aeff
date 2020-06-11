let parse_commands lexbuf =
    try Parser.commands Lexer.token lexbuf with
    | Parser.Error ->
        Error.syntax ~loc:(Location.of_lexeme (Lexing.lexeme_start_p lexbuf)) "parser error"
    | Failure failmsg when failmsg = "lexing: empty token" ->
        Error.syntax ~loc:(Location.of_lexeme (Lexing.lexeme_start_p lexbuf)) "unrecognised symbol."

type state = {
    desugarer : Desugarer.state;
    interpreter : Interpreter.state;
    typechecker : Typechecker.state;
    top_computations : Ast.computation list
}

let initial_state () =
    let load_function state (x, ty_sch, def) =
        let desugarer_state', x' = Desugarer.add_external_variable x state.desugarer in
        let interpreter_state' = Interpreter.add_external_function x' def state.interpreter in
        let typechecker_state' = Typechecker.add_external_function x' ty_sch state.typechecker in
        {state with desugarer = desugarer_state'; interpreter = interpreter_state'; typechecker = typechecker_state'}
    in
    {
        desugarer = Desugarer.initial_state;
        interpreter = Interpreter.initial_state;
        typechecker = Typechecker.initial_state;
        top_computations = []
    }
    |> fun state -> Utils.fold load_function state BuiltIn.functions


let execute_command state = function
| Ast.TyDef ty_defs ->
    let typechecker_state' = Typechecker.add_type_definitions state.typechecker ty_defs in
    {state with typechecker = typechecker_state'}

| Ast.TopLet (x, expr) ->
    let interpreter_state' = Interpreter.eval_top_let state.interpreter x expr in
    let typechecker_state' = Typechecker.add_top_definition state.typechecker x expr in
    {state with interpreter = interpreter_state'; typechecker = typechecker_state'}
| Ast.TopDo comp ->
    let _ = Typechecker.infer state.typechecker comp in
    {state with top_computations = comp :: state.top_computations}
| Ast.Operation (op, ty) ->
    let typechecker_state' = Typechecker.add_operation state.typechecker op ty in
    {state with typechecker = typechecker_state'}

module S = Tiny_httpd

let redirect basepath url =
  S.Response.make_raw ~headers:[("Location", Format.sprintf "%s%s" basepath url)] ~code:302 ""

let print_request req = ignore req
   (* Format.printf "%t@." (fun ppf -> S.Request.pp_ ppf req) *)

let make_process = function
    | [] -> Ast.Run (Ast.Return (Ast.Tuple []))
    | comp :: comps ->
        List.fold_left (fun proc comp -> Ast.Parallel (proc, Ast.Run comp)) (Ast.Run comp) comps

let run_server state0 =
  let server = S.create () in
  let basepath = Format.sprintf "http://%s:%d" (S.addr server) (S.port server) in
  let steps proc = Runner.top_steps state0.interpreter proc in
  let initial_process = make_process state0.top_computations in
  let state = ref [(initial_process, steps initial_process, [])] in
  let update_proc proc =
    let _, _, errors = List.nth !state 0 in
    state := (proc, steps proc, errors) :: !state
  and add_msg msg =
    let proc, steps, errors = List.nth !state 0 in
    state := (proc, steps, msg :: errors) :: !state
  in
  let both msg proc' =
    update_proc proc';
    add_msg msg
  in
  let top_step i =
    let (_, steps, _) = List.hd !state in
    match List.nth steps i with
    | Runner.Step proc -> update_proc proc
    | Runner.TopOut (op, expr, proc) ->
        Format.printf "out %t %t@." (Ast.Operation.print op) (Ast.print_expression expr);
        update_proc proc
  in
  let random_step () =
    let (_, steps, _) = List.hd !state in
    let i = Random.int (List.length steps) in
    top_step i
  in
  let many_steps num_steps =
    for _step = 1 to num_steps do
      random_step ()
    done
  in
  let view () =
    S.Response.make_string (Ok (View.show (List.nth !state 0)))
  in
  S.add_route_handler ~meth:`GET server
    S.Route.return (fun req -> print_request req; view ());
  S.add_route_handler ~meth:`GET server
    S.Route.(exact "step" @/ int @/ return) (fun i req ->
        print_request req;
        try
            top_step i;
            redirect basepath "/"
        with
        | Error.Error (_, _, msg) ->
            S.Response.make (Error (500, msg))
    );
  S.add_route_handler ~meth:`GET server
    S.Route.(exact "step" @/ exact "random" @/ int @/ return) (fun num_steps req ->
        print_request req;
        try
            many_steps num_steps;
            redirect basepath "/"
        with
        | Error.Error (_, _, msg) ->
            S.Response.make (Error (500, msg))
    );
  S.add_route_handler ~meth:`GET server
    S.Route.(exact "back" @/ return) (fun req ->
        print_request req;
        try
            (match !state with
            | [] -> ()
            | [_] -> ()
            | _ :: old_state -> state := old_state);
            redirect basepath "/"
        with
        | Error.Error (_, _, msg) ->
            S.Response.make (Error (500, msg))
    );
  S.add_route_handler ~meth:`GET server
    S.Route.(exact "operation" @/ return) (fun req ->
        print_request req;
        let params = S.Request.query req in
        try
            let input = List.assoc "operation" params in
            let lexbuf = Lexing.from_string input in
            let (op, term) = Parser.incoming_operation Lexer.token lexbuf in
            let op' = Desugarer.lookup_operation ~loc:term.Utils.at state0.desugarer op in
            let expr' = Desugarer.desugar_pure_expression state0.desugarer term in
            let (proc, _, _) = List.nth !state 0 in
            both
                (View.Info (Format.sprintf "Incoming operation %s" input))
                (Runner.incoming_operation proc op' expr');
            redirect basepath "/"
        with
        | Error.Error (_, _, msg) ->
            S.Response.make (Error (500, msg))
    );
  Format.printf "listening on %s/@." basepath;
  S.run server

let main () =
    match Array.to_list Sys.argv with
    | [] ->
        assert false
    | [_aeff] ->
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
