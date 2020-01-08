type comp_state =
  | Out of Ast.operation * Ast.expression * Ast.computation
  | Step of Ast.computation
  | Stuck

let comp_state state = function
  | Ast.Out (op, expr, comp) -> Out (op, expr, comp)
  | comp ->
        try Step (Interpreter.step state comp)
        with Interpreter.Stuck -> Stuck

let step_process state comps i =
    let comp = List.nth comps i in
    match comp_state state comp with
    | Stuck -> None
    | Step comp' ->
        Some (List.mapi (fun j comp'' -> if i = j then comp' else comp'') comps)
    | Out (op, expr, comp') ->
        Some (List.mapi (fun j comp'' -> if i = j then comp' else In (op, expr, comp'')) comps)

let random_step state comps =
    let steps =
        List.mapi (fun i _ -> step_process state comps i) comps
        |> List.filter_map (fun opt_step -> opt_step)
    in
    match steps with
    | [] -> None
    | _ ->
        let n = Random.int (List.length steps) in
        Some (List.nth steps n)

let incoming_operation state comps op comp =
    let expr = Interpreter.eval_expr state comp in
    List.map (fun comp -> Ast.In (op, expr, comp)) comps
