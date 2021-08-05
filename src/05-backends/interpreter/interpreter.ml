open Utils
module Ast = Language.Ast

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
  | PromiseSignal
  | InterruptReturn
  | InterruptSignal
  | InterruptPromise
  | InterruptPromise'
  | Match
  | ApplyFun
  | DoReturn
  | DoSignal
  | AwaitFulfill
  | Unbox
  | Spawn

type computation_reduction =
  | InterruptCtx of computation_reduction
  | SignalCtx of computation_reduction
  | DoCtx of computation_reduction
  | ComputationRedex of computation_redex

type process_redex =
  | RunSignal
  | RunSpawn
  | ParallelSignal1
  | ParallelSignal2
  | InterruptRun
  | InterruptParallel
  | InterruptSignal
  | TopSignal

type process_reduction =
  | LeftCtx of process_reduction
  | RightCtx of process_reduction
  | InterruptProcCtx of process_reduction
  | SignalProcCtx of process_reduction
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
  | Ast.PConst c when Language.Const.equal c (eval_const state expr) ->
      Ast.VariableMap.empty
  | Ast.PNonbinding -> Ast.VariableMap.empty
  | _ -> raise PatternMismatch

let rec remove_pattern_bound_variables subst = function
  | Ast.PVar x -> Ast.VariableMap.remove x subst
  | PAnnotated (pat, _) -> remove_pattern_bound_variables subst pat
  | PAs (pat, x) ->
      let subst = remove_pattern_bound_variables subst pat in
      Ast.VariableMap.remove x subst
  | PTuple pats -> List.fold_left remove_pattern_bound_variables subst pats
  | PVariant (_, None) -> subst
  | PVariant (_, Some pat) -> remove_pattern_bound_variables subst pat
  | PConst _ -> subst
  | PNonbinding -> subst

let rec refresh_pattern = function
  | Ast.PVar x ->
      let x' = Ast.Variable.refresh x in
      (Ast.PVar x', [ (x, x') ])
  | PAnnotated (pat, _) -> refresh_pattern pat
  | PAs (pat, x) ->
      let pat', vars = refresh_pattern pat in
      let x' = Ast.Variable.refresh x in
      (PAs (pat', x'), (x, x') :: vars)
  | PTuple pats ->
      let fold pat (pats', vars) =
        let pat', vars' = refresh_pattern pat in
        (pat' :: pats', vars' @ vars)
      in
      let pats', vars = List.fold_right fold pats ([], []) in
      (PTuple pats', vars)
  | PVariant (lbl, Some pat) ->
      let pat', vars = refresh_pattern pat in
      (PVariant (lbl, Some pat'), vars)
  | (PVariant (_, None) | PConst _ | PNonbinding) as pat -> (pat, [])

let rec refresh_expression vars = function
  | Ast.Var x as expr -> (
      match List.assoc_opt x vars with None -> expr | Some x' -> Var x' )
  | Const _ as expr -> expr
  | Annotated (expr, ty) -> Annotated (refresh_expression vars expr, ty)
  | Tuple exprs -> Tuple (List.map (refresh_expression vars) exprs)
  | Variant (label, expr) ->
      Variant (label, Option.map (refresh_expression vars) expr)
  | Lambda abs -> Lambda (refresh_abstraction vars abs)
  | RecLambda (x, abs) ->
      let x' = Ast.Variable.refresh x in
      RecLambda (x', refresh_abstraction ((x, x') :: vars) abs)
  | Fulfill expr -> Fulfill (refresh_expression vars expr)
  | Reference ref -> Reference ref
  | Boxed expr -> Boxed (refresh_expression vars expr)

and refresh_computation vars = function
  | Ast.Return expr -> Ast.Return (refresh_expression vars expr)
  | Do (comp, abs) ->
      Do (refresh_computation vars comp, refresh_abstraction vars abs)
  | Match (expr, cases) ->
      Match
        (refresh_expression vars expr, List.map (refresh_abstraction vars) cases)
  | Apply (expr1, expr2) ->
      Apply (refresh_expression vars expr1, refresh_expression vars expr2)
  | Operation (Signal (op, expr), comp) ->
      Operation
        ( Signal (op, refresh_expression vars expr),
          refresh_computation vars comp )
  | Operation (Promise (k, op, abs, p), comp) ->
      let p' = Ast.Variable.refresh p in
      let k', vars' =
        match k with
        | None -> (None, vars)
        | Some k'' ->
            let k''' = Ast.Variable.refresh k'' in
            (Some k''', (k'', k''') :: vars)
      in
      Operation
        ( Promise (k', op, refresh_abstraction vars' abs, p'),
          refresh_computation ((p, p') :: vars) comp )
  | Operation (Spawn comp1, comp2) ->
      Operation
        (Spawn (refresh_computation vars comp1), refresh_computation vars comp2)
  | Interrupt (op, expr, comp) ->
      Interrupt (op, refresh_expression vars expr, refresh_computation vars comp)
  | Await (expr, abs) ->
      Await (refresh_expression vars expr, refresh_abstraction vars abs)
  | Unbox (expr, abs) ->
      Unbox (refresh_expression vars expr, refresh_abstraction vars abs)

and refresh_abstraction vars (pat, comp) =
  let pat', vars' = refresh_pattern pat in
  (pat', refresh_computation (vars @ vars') comp)

let rec substitute_expression subst = function
  | Ast.Var x as expr -> (
      match Ast.VariableMap.find_opt x subst with
      | None -> expr
      | Some expr -> expr )
  | Const _ as expr -> expr
  | Annotated (expr, ty) -> Annotated (substitute_expression subst expr, ty)
  | Tuple exprs -> Tuple (List.map (substitute_expression subst) exprs)
  | Variant (label, expr) ->
      Variant (label, Option.map (substitute_expression subst) expr)
  | Lambda abs -> Lambda (substitute_abstraction subst abs)
  | RecLambda (x, abs) -> RecLambda (x, substitute_abstraction subst abs)
  | Fulfill expr -> Fulfill (substitute_expression subst expr)
  | Reference ref -> Reference ref
  | Boxed expr -> Boxed (substitute_expression subst expr)

and substitute_computation subst = function
  | Ast.Return expr -> Ast.Return (substitute_expression subst expr)
  | Do (comp, abs) ->
      Do (substitute_computation subst comp, substitute_abstraction subst abs)
  | Match (expr, cases) ->
      Match
        ( substitute_expression subst expr,
          List.map (substitute_abstraction subst) cases )
  | Apply (expr1, expr2) ->
      Apply
        (substitute_expression subst expr1, substitute_expression subst expr2)
  | Operation (Signal (op, expr), comp) ->
      Operation
        ( Signal (op, substitute_expression subst expr),
          substitute_computation subst comp )
  | Operation (Promise (k, op, abs, p), comp) ->
      let subst' = remove_pattern_bound_variables subst (PVar p) in
      Operation
        ( Promise (k, op, substitute_abstraction subst abs, p),
          substitute_computation subst' comp )
  | Operation (Spawn comp1, comp2) ->
      Operation
        ( Spawn (substitute_computation subst comp1),
          substitute_computation subst comp2 )
  | Interrupt (op, expr, comp) ->
      Interrupt
        (op, substitute_expression subst expr, substitute_computation subst comp)
  | Await (expr, abs) ->
      Await (substitute_expression subst expr, substitute_abstraction subst abs)
  | Unbox (expr, abs) ->
      Unbox (substitute_expression subst expr, substitute_abstraction subst abs)

and substitute_abstraction subst (pat, comp) =
  let subst' = remove_pattern_bound_variables subst pat in
  (pat, substitute_computation subst' comp)

let substitute subst comp =
  let subst = Ast.VariableMap.map (refresh_expression []) subst in
  substitute_computation subst comp

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
  | Ast.Operation ((Ast.Promise (k, op, op_comp, p) as out), comp) -> (
      let comps' =
        step_in_context step_computation state
          (fun red -> SignalCtx red)
          (fun comp' -> Ast.Operation (out, comp'))
          comp
      in
      match comp with
      | Ast.Operation (Ast.Promise _, _) -> comps'
      | Ast.Operation (out, cont') ->
          ( ComputationRedex PromiseSignal,
            Ast.Operation
              (out, Ast.Operation (Ast.Promise (k, op, op_comp, p), cont')) )
          :: comps'
      | _ -> comps' )
  | Ast.Operation (out, comp) ->
      step_in_context step_computation state
        (fun red -> SignalCtx red)
        (fun comp' -> Ast.Operation (out, comp'))
        comp
  | Ast.Interrupt (op, expr, comp) -> (
      let comps' =
        step_in_context step_computation state
          (fun red -> InterruptCtx red)
          (fun comp' -> Ast.Interrupt (op, expr, comp'))
          comp
      in
      match comp with
      | Ast.Return expr ->
          (ComputationRedex InterruptReturn, Ast.Return expr) :: comps'
      | Ast.Operation (out, comp) ->
          (ComputationRedex InterruptSignal, step_in_out state op expr comp out)
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
      | Ast.Operation (out, comp1') ->
          ( ComputationRedex DoSignal,
            Ast.Operation (out, Ast.Do (comp1', comp2)) )
          :: comps1'
      | _ -> comps1' )
  | Ast.Await (expr, (pat, comp)) -> (
      match expr with
      | Ast.Fulfill expr ->
          let subst = match_pattern_with_expression state pat expr in
          [ (ComputationRedex AwaitFulfill, substitute subst comp) ]
      | _ -> [] )
  | Ast.Unbox (expr, (pat, comp)) -> (
      match expr with
      | Ast.Boxed expr ->
          let subst = match_pattern_with_expression state pat expr in
          [ (ComputationRedex Unbox, substitute subst comp) ]
      | Ast.Var x ->
          let expr' = Ast.VariableMap.find x state.variables in
          [ (ComputationRedex Unbox, Ast.Unbox (expr', (pat, comp))) ]
      | _ ->
          Error.runtime "Expected boxed expresion but got %t instead."
            (Ast.print_expression expr) )

and step_in_out state op expr cont = function
  | Ast.Signal (op', expr') ->
      Ast.Operation (Ast.Signal (op', expr'), Ast.Interrupt (op, expr, cont))
  | Ast.Promise (k, op', (arg_pat, op_comp), p) when op = op' ->
      let subst = match_pattern_with_expression state arg_pat expr in
      let comp' = substitute subst op_comp in

      let p' = Ast.Variable.fresh "p'" in

      let comp'' =
        match k with
        | None -> comp'
        | Some k' ->
            let f =
              Ast.Lambda
                ( Ast.PTuple [],
                  Ast.Operation
                    ( Ast.Promise (k, op', (arg_pat, op_comp), p'),
                      Ast.Return (Ast.Var p') ) )
            in
            substitute
              (match_pattern_with_expression state (Ast.PVar k') f)
              comp'
      in
      Ast.Do (comp'', (Ast.PVar p, Ast.Interrupt (op, expr, cont)))
  | Ast.Promise (k, op', op_comp, p) ->
      Ast.Operation
        (Ast.Promise (k, op', op_comp, p), Ast.Interrupt (op, expr, cont))
  | Ast.Spawn comp ->
      Ast.Operation (Ast.Spawn comp, Ast.Interrupt (op, expr, cont))

let rec step_process state = function
  | Ast.Run comp -> (
      let comps' =
        step_computation state comp
        |> List.map (fun (red, comp') -> (RunCtx red, Ast.Run comp'))
      in
      match comp with
      | Ast.Operation (Ast.Signal (op, expr), comp') ->
          (ProcessRedex RunSignal, Ast.SignalProc (op, expr, Ast.Run comp'))
          :: comps'
      | Ast.Operation (Ast.Spawn comp1, comp2) ->
          (ProcessRedex RunSpawn, Ast.Parallel (Ast.Run comp1, Ast.Run comp2))
          :: (ProcessRedex RunSpawn, Ast.Parallel (Ast.Run comp2, Ast.Run comp1))
          :: comps'
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
        | Ast.SignalProc (op, expr, proc1') ->
            ( ProcessRedex ParallelSignal1,
              Ast.SignalProc
                ( op,
                  expr,
                  Ast.Parallel (proc1', Ast.InterruptProc (op, expr, proc2)) )
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
        | Ast.SignalProc (op, expr, proc2') ->
            ( ProcessRedex ParallelSignal2,
              Ast.SignalProc
                ( op,
                  expr,
                  Ast.Parallel (Ast.InterruptProc (op, expr, proc1), proc2') )
            )
            :: procs'
        | _ -> procs'
      in
      proc1_first @ proc2_first
  | Ast.InterruptProc (op, expr, proc) -> (
      let procs' =
        step_in_context step_process state
          (fun red -> InterruptProcCtx red)
          (fun proc' -> Ast.InterruptProc (op, expr, proc'))
          proc
      in
      match proc with
      | Ast.Run comp ->
          (ProcessRedex InterruptRun, Ast.Run (Ast.Interrupt (op, expr, comp)))
          :: procs'
      | Ast.Parallel (proc1, proc2) ->
          ( ProcessRedex InterruptParallel,
            Ast.Parallel
              ( Ast.InterruptProc (op, expr, proc1),
                Ast.InterruptProc (op, expr, proc2) ) )
          :: procs'
      | Ast.SignalProc (op', expr', proc') ->
          ( ProcessRedex InterruptSignal,
            Ast.SignalProc (op', expr', Ast.InterruptProc (op, expr, proc')) )
          :: procs'
      | _ -> procs' )
  | Ast.SignalProc (op, expr, proc) ->
      step_in_context step_process state
        (fun red -> SignalProcCtx red)
        (fun proc' -> Ast.SignalProc (op, expr, proc'))
        proc

let incoming_operation proc op expr = Ast.InterruptProc (op, expr, proc)

let eval_top_let state x expr =
  { state with variables = Ast.VariableMap.add x expr state.variables }

let add_external_function x def state =
  {
    state with
    builtin_functions = Ast.VariableMap.add x def state.builtin_functions;
  }

type top_step =
  | TopSignal of Ast.opsym * Ast.expression * Ast.process
  | Step of Ast.process

let top_steps state proc =
  let steps =
    step_process state proc |> List.map (fun (red, proc) -> (red, Step proc))
  in
  match proc with
  | Ast.SignalProc (op, expr, proc) ->
      (ProcessRedex TopSignal, TopSignal (op, expr, proc)) :: steps
  | _ -> steps
