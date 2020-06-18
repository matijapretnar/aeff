type redex =
  | RunOut
  | ParallelOut1
  | ParallelOut2
  | InRun
  | InParallel
  | InOut
  | TopOut

type reduction =
  | LeftCtx of reduction
  | RightCtx of reduction
  | InCtx of reduction
  | OutCtx of reduction
  | RunCtx of Interpreter.reduction
  | Redex of redex

let rec step state = function
  | Ast.Run comp -> (
      let comps' =
        Interpreter.step state comp
        |> List.map (fun (red, comp') -> (RunCtx red, Ast.Run comp'))
      in
      match comp with
      | Ast.Out (op, expr, comp') ->
          (Redex RunOut, Ast.OutProc (op, expr, Ast.Run comp')) :: comps'
      | _ -> comps' )
  | Ast.Parallel (proc1, proc2) ->
      let proc1_first =
        let procs' =
          step_in_context state
            (fun red -> LeftCtx red)
            (fun proc1' -> Ast.Parallel (proc1', proc2))
            proc1
        in
        match proc1 with
        | Ast.OutProc (op, expr, proc1') ->
            ( Redex ParallelOut1,
              Ast.OutProc
                (op, expr, Ast.Parallel (proc1', Ast.InProc (op, expr, proc2)))
            )
            :: procs'
        | _ -> procs'
      and proc2_first =
        let procs' =
          step_in_context state
            (fun red -> RightCtx red)
            (fun proc2' -> Ast.Parallel (proc1, proc2'))
            proc2
        in
        match proc2 with
        | Ast.OutProc (op, expr, proc2') ->
            ( Redex ParallelOut2,
              Ast.OutProc
                (op, expr, Ast.Parallel (Ast.InProc (op, expr, proc1), proc2'))
            )
            :: procs'
        | _ -> procs'
      in
      proc1_first @ proc2_first
  | Ast.InProc (op, expr, proc) -> (
      let procs' =
        step_in_context state
          (fun red -> InCtx red)
          (fun proc' -> Ast.InProc (op, expr, proc'))
          proc
      in
      match proc with
      | Ast.Run comp ->
          (Redex InRun, Ast.Run (Ast.In (op, expr, comp))) :: procs'
      | Ast.Parallel (proc1, proc2) ->
          ( Redex InParallel,
            Ast.Parallel
              (Ast.InProc (op, expr, proc1), Ast.InProc (op, expr, proc2)) )
          :: procs'
      | Ast.OutProc (op', expr', proc') ->
          (Redex InOut, Ast.OutProc (op', expr', Ast.InProc (op, expr, proc')))
          :: procs'
      | _ -> procs' )
  | Ast.OutProc (op, expr, proc) ->
      step_in_context state
        (fun red -> OutCtx red)
        (fun proc' -> Ast.OutProc (op, expr, proc'))
        proc

and step_in_context state redCtx ctx proc =
  let procs' = step state proc in
  List.map (fun (red, proc') -> (redCtx red, ctx proc')) procs'

type top_step =
  | TopOut of Ast.operation * Ast.expression * Ast.process
  | Step of Ast.process

let top_steps state proc =
  let steps =
    step state proc |> List.map (fun (red, proc) -> (red, Step proc))
  in
  match proc with
  | Ast.OutProc (op, expr, proc) ->
      (Redex TopOut, TopOut (op, expr, proc)) :: steps
  | _ -> steps

let incoming_operation proc op expr = Ast.InProc (op, expr, proc)
