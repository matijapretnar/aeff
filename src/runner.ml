let rec hoist_op = function
  | Ast.Out (op, expr, comp) -> Some (op, expr, comp)
  | Ast.Handler (op', abs, p, comp) -> (
      match hoist_op comp with
      | Some (op, expr, comp') ->
          Some (op, expr, Ast.Handler (op', abs, p, comp'))
      | None -> None )
  | _ -> None

let rec step state = function
  | Ast.Run comp -> (
      let comps' =
        Interpreter.step state comp
        |> List.map (fun (path, comp') -> (path, Ast.Run comp'))
      in
      match hoist_op comp with
      | None -> comps'
      | Some (op, expr, comp') ->
          ([ "runOut" ], Ast.OutProc (op, expr, Ast.Run comp')) :: comps' )
  | Ast.Parallel (proc1, proc2) ->
      let proc1_first =
        let procs' =
          step_in_context state "left"
            (fun proc1' -> Ast.Parallel (proc1', proc2))
            proc1
        in
        match proc1 with
        | Ast.OutProc (op, expr, proc1') ->
            ( [ "leftOut" ],
              Ast.OutProc
                (op, expr, Ast.Parallel (proc1', Ast.InProc (op, expr, proc2)))
            )
            :: procs'
        | _ -> procs'
      and proc2_first =
        let procs' =
          step_in_context state "right"
            (fun proc2' -> Ast.Parallel (proc1, proc2'))
            proc2
        in
        match proc2 with
        | Ast.OutProc (op, expr, proc2') ->
            ( [ "rightOut" ],
              Ast.OutProc
                (op, expr, Ast.Parallel (Ast.InProc (op, expr, proc1), proc2'))
            )
            :: procs'
        | _ -> procs'
      in
      proc1_first @ proc2_first
  | Ast.InProc (op, expr, proc) -> (
      let procs' =
        step_in_context state "in"
          (fun proc' -> Ast.InProc (op, expr, proc'))
          proc
      in
      match proc with
      | Ast.Run comp ->
          ([ "inRun" ], Ast.Run (Ast.In (op, expr, comp))) :: procs'
      | Ast.Parallel (proc1, proc2) ->
          ( [ "inParallel" ],
            Ast.Parallel
              (Ast.InProc (op, expr, proc1), Ast.InProc (op, expr, proc2)) )
          :: procs'
      | Ast.OutProc (op', expr', proc') ->
          ([ "inOut" ], Ast.OutProc (op', expr', Ast.InProc (op, expr, proc')))
          :: procs'
      | _ -> procs' )
  | Ast.OutProc (op, expr, proc) ->
      step_in_context state "out"
        (fun proc' -> Ast.OutProc (op, expr, proc'))
        proc

and step_in_context state label ctx proc =
  let procs' = step state proc in
  List.map (fun (path, proc') -> (label :: path, ctx proc')) procs'

type top_step =
  | TopOut of Ast.operation * Ast.expression * Ast.process
  | Step of Ast.process

let top_steps state proc =
  let steps =
    step state proc |> List.map (fun (path, proc) -> (path, Step proc))
  in
  match proc with
  | Ast.OutProc (op, expr, proc) ->
      ([ "topOut" ], TopOut (op, expr, proc)) :: steps
  | _ -> steps

let incoming_operation proc op expr = Ast.InProc (op, expr, proc)
