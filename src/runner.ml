let rec hoist_op = function
  | Ast.Out (op, expr, comp) -> Some (op, expr, comp)
  | Ast.Handler (op', abs, p, comp) ->
      begin match hoist_op comp with
      | Some (op, expr, comp') -> Some (op, expr, Ast.Handler (op', abs, p, comp'))
      | None -> None
      end
  | _ -> None

let rec step state = function
  | Ast.Run comp ->
      let comps' = Interpreter.step state comp |> List.map (fun comp' -> Ast.Run comp') in
      begin match hoist_op comp with
      | None -> comps'
      | Some (op, expr, comp') -> Ast.OutProc (op, expr, Ast.Run comp') :: comps'
      end
  | Ast.Parallel (proc1, proc2) ->
      let proc1_first =
        let procs' = step state proc1 |> List.map (fun proc1' -> Ast.Parallel (proc1', proc2)) in
        begin match proc1 with
        | Ast.OutProc (op, expr, proc1') ->
            Ast.OutProc (op, expr, Ast.Parallel (proc1', Ast.InProc (op, expr, proc2))) :: procs'
        | _ -> procs'
        end
      and proc2_first =
        let procs' = step state proc2 |> List.map (fun proc2' -> Ast.Parallel (proc1, proc2')) in
        begin match proc2 with
        | Ast.OutProc (op, expr, proc2') ->
            Ast.OutProc (op, expr, Ast.Parallel (Ast.InProc (op, expr, proc1), proc2')) :: procs'
        | _ -> procs'
        end
      in
      proc1_first @ proc2_first
  | Ast.InProc (op, expr, proc) ->
      let procs' = step state proc |> List.map (fun proc' -> Ast.InProc (op, expr, proc')) in
      begin match proc with
      | Ast.Run comp -> Ast.Run (Ast.In (op, expr, comp)) :: procs'
      | Ast.Parallel (proc1, proc2) -> Ast.Parallel (Ast.InProc (op, expr, proc1), Ast.InProc (op, expr, proc2)) :: procs'
      | Ast.OutProc (op', expr', proc') -> Ast.OutProc (op', expr', Ast.InProc (op, expr, proc')) :: procs'
      | _ -> procs'
      end
  | Ast.OutProc (op, expr, proc) ->
      step state proc
      |> List.map (fun proc' -> Ast.OutProc (op, expr, proc'))
  
type top_step =
  | TopOut of Ast.operation * Ast.expression * Ast.process
  | Step of Ast.process

let top_steps state proc =
    let steps =
      step state proc |> List.map (fun proc -> Step proc)
    in
    match proc with
    | Ast.OutProc (op, expr, proc) ->
        TopOut (op, expr, proc) :: steps
    | _ -> steps

let incoming_operation proc op expr =
    Ast.InProc (op, expr, proc)
