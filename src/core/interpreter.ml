open Utils

type state = {
  variables : Ast.expression Ast.VariableMap.t;
  builtin_functions : (Ast.expression -> Ast.computation) Ast.VariableMap.t;
}

let initial_state =
  {
    variables = Ast.VariableMap.empty;
    builtin_functions = Ast.VariableMap.empty;
  }

exception PatternMismatch

type computation_redex =
  | PromiseOut
  | InReturn
  | InOut
  | InPromise
  | InPromise'
  | Match
  | ApplyFun
  | DoReturn
  | DoOut
  | DoPromise
  | AwaitFulfill

type computation_reduction =
  | PromiseCtx of computation_reduction
  | InCtx of computation_reduction
  | OutCtx of computation_reduction
  | DoCtx of computation_reduction
  | ComputationRedex of computation_redex

type process_redex =
  | RunOut
  | ParallelOut1
  | ParallelOut2
  | InRun
  | InParallel
  | InOut
  | TopOut

type process_reduction =
  | LeftCtx of process_reduction
  | RightCtx of process_reduction
  | InProcCtx of process_reduction
  | OutProcCtx of process_reduction
  | RunCtx of computation_reduction
  | ProcessRedex of process_redex

let rec eval_tuple state = function
  | Ast.Tuple exprs -> exprs
  | Ast.Var x -> eval_tuple state (Ast.VariableMap.find x state.variables)
  | expr ->
      Error.runtime "Tuple expected but got %t" (Ast.print_expression expr)

let rec eval_variant state = function
  | Ast.Variant (lbl, expr) -> (lbl, expr)
  | Ast.Var x -> eval_variant state (Ast.VariableMap.find x state.variables)
  | expr ->
      Error.runtime "Variant expected but got %t" (Ast.print_expression expr)

let rec eval_const state = function
  | Ast.Const c -> c
  | Ast.Var x -> eval_const state (Ast.VariableMap.find x state.variables)
  | expr ->
      Error.runtime "Const expected but got %t" (Ast.print_expression expr)

let rec match_pattern_with_expression state pat expr =
  match pat with
  | Ast.PVar x -> Ast.VariableMap.singleton x expr
  | Ast.PAnnotated (pat, _) -> match_pattern_with_expression state pat expr
  | Ast.PAs (pat, x) ->
      let subst = match_pattern_with_expression state pat expr in
      Ast.VariableMap.add x expr subst
  | Ast.PTuple pats ->
      let exprs = eval_tuple state expr in
      List.fold_left2
        (fun subst pat expr ->
          let subst' = match_pattern_with_expression state pat expr in
          Ast.VariableMap.union (fun _ _ _ -> assert false) subst subst')
        Ast.VariableMap.empty pats exprs
  | Ast.PVariant (label, pat) -> (
      match (pat, eval_variant state expr) with
      | None, (label', None) when label = label' -> Ast.VariableMap.empty
      | Some pat, (label', Some expr) when label = label' ->
          match_pattern_with_expression state pat expr
      | _, _ -> raise PatternMismatch )
  | Ast.PConst c when Const.equal c (eval_const state expr) ->
      Ast.VariableMap.empty
  | Ast.PNonbinding -> Ast.VariableMap.empty
  | _ -> raise PatternMismatch

let substitute subst comp =
  let subst = Ast.VariableMap.map (Ast.refresh_expression []) subst in
  Ast.substitute_computation subst comp

let rec eval_function state = function
  | Ast.Lambda (pat, comp) ->
      fun arg ->
        let subst = match_pattern_with_expression state pat arg in
        substitute subst comp
  | Ast.RecLambda (f, (pat, comp)) as expr ->
      fun arg ->
        let subst =
          match_pattern_with_expression state pat arg
          |> Ast.VariableMap.add f expr
        in
        substitute subst comp
  | Ast.Var x -> (
      match Ast.VariableMap.find_opt x state.variables with
      | Some expr -> eval_function state expr
      | None -> Ast.VariableMap.find x state.builtin_functions )
  | expr ->
      Error.runtime "Function expected but got %t" (Ast.print_expression expr)

let step_in_context step state redCtx ctx term =
  let terms' = step state term in
  List.map (fun (red, term') -> (redCtx red, ctx term')) terms'

let rec step_computation state = function
  | Ast.Return _ -> []
  | Ast.Out (op, expr, comp) ->
      step_in_context step_computation state
        (fun red -> OutCtx red)
        (fun comp' -> Ast.Out (op, expr, comp'))
        comp
  | Ast.Promise (op, op_comp, p, comp) -> (
      let comps' =
        step_in_context step_computation state
          (fun red -> PromiseCtx red)
          (fun comp' -> Ast.Promise (op, op_comp, p, comp'))
          comp
      in
      match comp with
      | Ast.Out (op', expr', cont') ->
          ( ComputationRedex PromiseOut,
            Ast.Out (op', expr', Ast.Promise (op, op_comp, p, cont')) )
          :: comps'
      | _ -> comps' )
  | Ast.In (op, expr, comp) -> (
      let comps' =
        step_in_context step_computation state
          (fun red -> InCtx red)
          (fun comp' -> Ast.In (op, expr, comp'))
          comp
      in
      match comp with
      | Ast.Return expr ->
          (ComputationRedex InReturn, Ast.Return expr) :: comps'
      | Ast.Out (op', expr', cont') ->
          ( ComputationRedex InOut,
            Ast.Out (op', expr', Ast.In (op, expr, cont')) )
          :: comps'
      | Ast.Promise (op', (arg_pat, op_comp), p, comp) when op = op' ->
          let subst = match_pattern_with_expression state arg_pat expr in
          let y = Ast.Variable.fresh "y" in
          let comp' =
            Ast.Do
              ( substitute subst op_comp,
                ( Ast.PVar y,
                  Ast.Do
                    ( Ast.Return (Ast.Var y),
                      (Ast.PVar p, Ast.In (op, expr, comp)) ) ) )
          in
          (ComputationRedex InPromise, comp') :: comps'
      | Ast.Promise (op', op_comp, p, comp) ->
          ( ComputationRedex InPromise',
            Ast.Promise (op', op_comp, p, Ast.In (op, expr, comp)) )
          :: comps'
      | _ -> comps' )
  | Ast.Match (expr, cases) ->
      let rec find_case = function
        | (pat, comp) :: cases -> (
            match match_pattern_with_expression state pat expr with
            | subst -> [ (ComputationRedex Match, substitute subst comp) ]
            | exception PatternMismatch -> find_case cases )
        | [] -> []
      in
      find_case cases
  | Ast.Apply (expr1, expr2) ->
      let f = eval_function state expr1 in
      [ (ComputationRedex ApplyFun, f expr2) ]
  | Ast.Do (comp1, comp2) -> (
      let comps1' =
        step_in_context step_computation state
          (fun red -> DoCtx red)
          (fun comp1' -> Ast.Do (comp1', comp2))
          comp1
      in
      match comp1 with
      | Ast.Return expr ->
          let pat, comp2' = comp2 in
          let subst = match_pattern_with_expression state pat expr in
          (ComputationRedex DoReturn, substitute subst comp2') :: comps1'
      | Ast.Out (op, expr, comp1) ->
          (ComputationRedex DoOut, Ast.Out (op, expr, Ast.Do (comp1, comp2)))
          :: comps1'
      | Ast.Promise (op, op_comp, pat, comp1) ->
          ( ComputationRedex DoPromise,
            Ast.Promise (op, op_comp, pat, Ast.Do (comp1, comp2)) )
          :: comps1'
      | _ -> comps1' )
  | Ast.Await (expr, (pat, comp)) -> (
      match expr with
      | Ast.Fulfill expr ->
          let subst = match_pattern_with_expression state pat expr in
          [ (ComputationRedex AwaitFulfill, substitute subst comp) ]
      | _ -> [] )

let rec step_process state = function
  | Ast.Run comp -> (
      let comps' =
        step_computation state comp
        |> List.map (fun (red, comp') -> (RunCtx red, Ast.Run comp'))
      in
      match comp with
      | Ast.Out (op, expr, comp') ->
          (ProcessRedex RunOut, Ast.OutProc (op, expr, Ast.Run comp')) :: comps'
      | _ -> comps' )
  | Ast.Parallel (proc1, proc2) ->
      let proc1_first =
        let procs' =
          step_in_context step_process state
            (fun red -> LeftCtx red)
            (fun proc1' -> Ast.Parallel (proc1', proc2))
            proc1
        in
        match proc1 with
        | Ast.OutProc (op, expr, proc1') ->
            ( ProcessRedex ParallelOut1,
              Ast.OutProc
                (op, expr, Ast.Parallel (proc1', Ast.InProc (op, expr, proc2)))
            )
            :: procs'
        | _ -> procs'
      and proc2_first =
        let procs' =
          step_in_context step_process state
            (fun red -> RightCtx red)
            (fun proc2' -> Ast.Parallel (proc1, proc2'))
            proc2
        in
        match proc2 with
        | Ast.OutProc (op, expr, proc2') ->
            ( ProcessRedex ParallelOut2,
              Ast.OutProc
                (op, expr, Ast.Parallel (Ast.InProc (op, expr, proc1), proc2'))
            )
            :: procs'
        | _ -> procs'
      in
      proc1_first @ proc2_first
  | Ast.InProc (op, expr, proc) -> (
      let procs' =
        step_in_context step_process state
          (fun red -> InProcCtx red)
          (fun proc' -> Ast.InProc (op, expr, proc'))
          proc
      in
      match proc with
      | Ast.Run comp ->
          (ProcessRedex InRun, Ast.Run (Ast.In (op, expr, comp))) :: procs'
      | Ast.Parallel (proc1, proc2) ->
          ( ProcessRedex InParallel,
            Ast.Parallel
              (Ast.InProc (op, expr, proc1), Ast.InProc (op, expr, proc2)) )
          :: procs'
      | Ast.OutProc (op', expr', proc') ->
          ( ProcessRedex InOut,
            Ast.OutProc (op', expr', Ast.InProc (op, expr, proc')) )
          :: procs'
      | _ -> procs' )
  | Ast.OutProc (op, expr, proc) ->
      step_in_context step_process state
        (fun red -> OutProcCtx red)
        (fun proc' -> Ast.OutProc (op, expr, proc'))
        proc

let incoming_operation proc op expr = Ast.InProc (op, expr, proc)

let eval_top_let state x expr =
  { state with variables = Ast.VariableMap.add x expr state.variables }

let add_external_function x def state =
  {
    state with
    builtin_functions = Ast.VariableMap.add x def state.builtin_functions;
  }

type top_step =
  | TopOut of Ast.operation * Ast.expression * Ast.process
  | Step of Ast.process

let top_steps state proc =
  let steps =
    step_process state proc |> List.map (fun (red, proc) -> (red, Step proc))
  in
  match proc with
  | Ast.OutProc (op, expr, proc) ->
      (ProcessRedex TopOut, TopOut (op, expr, proc)) :: steps
  | _ -> steps
