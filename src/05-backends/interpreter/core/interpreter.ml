open Utils
module Ast = Language.Ast
module Const = Language.Const

type environment = {
  variables : Ast.expression Ast.VariableMap.t;
  builtin_functions : (Ast.expression -> Ast.computation) Ast.VariableMap.t;
}

let initial_environment =
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

type process_reduction =
  | LeftCtx of process_reduction
  | RightCtx of process_reduction
  | InterruptProcCtx of process_reduction
  | SignalProcCtx of process_reduction
  | RunCtx of computation_reduction
  | ProcessRedex of process_redex

let rec eval_tuple env = function
  | Ast.Tuple exprs -> exprs
  | Ast.Var x -> eval_tuple env (Ast.VariableMap.find x env.variables)
  | expr ->
      Error.runtime "Tuple expected but got %t" (Ast.print_expression expr)

let rec eval_variant env = function
  | Ast.Variant (lbl, expr) -> (lbl, expr)
  | Ast.Var x -> eval_variant env (Ast.VariableMap.find x env.variables)
  | expr ->
      Error.runtime "Variant expected but got %t" (Ast.print_expression expr)

let rec eval_const env = function
  | Ast.Const c -> c
  | Ast.Var x -> eval_const env (Ast.VariableMap.find x env.variables)
  | expr ->
      Error.runtime "Const expected but got %t" (Ast.print_expression expr)

let rec match_pattern_with_expression env pat expr =
  match pat with
  | Ast.PVar x -> Ast.VariableMap.singleton x expr
  | Ast.PAnnotated (pat, _) -> match_pattern_with_expression env pat expr
  | Ast.PAs (pat, x) ->
      let subst = match_pattern_with_expression env pat expr in
      Ast.VariableMap.add x expr subst
  | Ast.PTuple pats ->
      let exprs = eval_tuple env expr in
      List.fold_left2
        (fun subst pat expr ->
          let subst' = match_pattern_with_expression env pat expr in
          Ast.VariableMap.union (fun _ _ _ -> assert false) subst subst')
        Ast.VariableMap.empty pats exprs
  | Ast.PVariant (label, pat) -> (
      match (pat, eval_variant env expr) with
      | None, (label', None) when label = label' -> Ast.VariableMap.empty
      | Some pat, (label', Some expr) when label = label' ->
          match_pattern_with_expression env pat expr
      | _, _ -> raise PatternMismatch)
  | Ast.PConst c when Const.equal c (eval_const env expr) ->
      Ast.VariableMap.empty
  | Ast.PNonbinding -> Ast.VariableMap.empty
  | _ -> raise PatternMismatch

let rec remove_pattern_bound_variables subst = function
  | Ast.PVar x -> Ast.VariableMap.remove x subst
  | Ast.PAnnotated (pat, _) -> remove_pattern_bound_variables subst pat
  | Ast.PAs (pat, x) ->
      let subst = remove_pattern_bound_variables subst pat in
      Ast.VariableMap.remove x subst
  | Ast.PTuple pats -> List.fold_left remove_pattern_bound_variables subst pats
  | Ast.PVariant (_, None) -> subst
  | Ast.PVariant (_, Some pat) -> remove_pattern_bound_variables subst pat
  | Ast.PConst _ -> subst
  | Ast.PNonbinding -> subst

let rec refresh_pattern = function
  | Ast.PVar x ->
      let x' = Ast.Variable.refresh x in
      (Ast.PVar x', [ (x, x') ])
  | Ast.PAnnotated (pat, _) -> refresh_pattern pat
  | Ast.PAs (pat, x) ->
      let pat', vars = refresh_pattern pat in
      let x' = Ast.Variable.refresh x in
      (Ast.PAs (pat', x'), (x, x') :: vars)
  | Ast.PTuple pats ->
      let fold pat (pats', vars) =
        let pat', vars' = refresh_pattern pat in
        (pat' :: pats', vars' @ vars)
      in
      let pats', vars = List.fold_right fold pats ([], []) in
      (Ast.PTuple pats', vars)
  | Ast.PVariant (lbl, Some pat) ->
      let pat', vars = refresh_pattern pat in
      (PVariant (lbl, Some pat'), vars)
  | (PVariant (_, None) | PConst _ | PNonbinding) as pat -> (pat, [])

let rec refresh_expression vars = function
  | Ast.Var x as expr -> (
      match List.assoc_opt x vars with None -> expr | Some x' -> Var x')
  | Ast.Const _ as expr -> expr
  | Ast.Annotated (expr, ty) -> Annotated (refresh_expression vars expr, ty)
  | Ast.Tuple exprs -> Tuple (List.map (refresh_expression vars) exprs)
  | Ast.Variant (label, expr) ->
      Variant (label, Option.map (refresh_expression vars) expr)
  | Ast.Lambda abs -> Lambda (refresh_abstraction vars abs)
  | Ast.RecLambda (x, abs) ->
      let x' = Ast.Variable.refresh x in
      RecLambda (x', refresh_abstraction ((x, x') :: vars) abs)
  | Ast.Fulfill expr -> Fulfill (refresh_expression vars expr)
  | Ast.Reference ref -> Reference ref
  | Ast.Boxed expr -> Boxed (refresh_expression vars expr)

and refresh_computation vars = function
  | Ast.Return expr -> Ast.Return (refresh_expression vars expr)
  | Ast.Do (comp, abs) ->
      Ast.Do (refresh_computation vars comp, refresh_abstraction vars abs)
  | Ast.Match (expr, cases) ->
      Ast.Match
        (refresh_expression vars expr, List.map (refresh_abstraction vars) cases)
  | Ast.Apply (expr1, expr2) ->
      Ast.Apply (refresh_expression vars expr1, refresh_expression vars expr2)
  | Ast.Operation (Signal (op, expr), comp) ->
      Ast.Operation
        ( Signal (op, refresh_expression vars expr),
          refresh_computation vars comp )
  | Ast.Operation (Promise (k, op, abs, p), comp) ->
      let p' = Ast.Variable.refresh p in
      let k', vars' =
        match k with
        | None -> (None, vars)
        | Some k'' ->
            let k''' = Ast.Variable.refresh k'' in
            (Some k''', (k'', k''') :: vars)
      in
      Ast.Operation
        ( Promise (k', op, refresh_abstraction vars' abs, p'),
          refresh_computation ((p, p') :: vars) comp )
  | Ast.Operation (Spawn comp1, comp2) ->
      Ast.Operation
        (Spawn (refresh_computation vars comp1), refresh_computation vars comp2)
  | Ast.Interrupt (op, expr, comp) ->
      Ast.Interrupt
        (op, refresh_expression vars expr, refresh_computation vars comp)
  | Ast.Await (expr, abs) ->
      Ast.Await (refresh_expression vars expr, refresh_abstraction vars abs)
  | Ast.Unbox (expr, abs) ->
      Ast.Unbox (refresh_expression vars expr, refresh_abstraction vars abs)

and refresh_abstraction vars (pat, comp) =
  let pat', vars' = refresh_pattern pat in
  (pat', refresh_computation (vars @ vars') comp)

let rec substitute_expression subst = function
  | Ast.Var x as expr -> (
      match Ast.VariableMap.find_opt x subst with
      | None -> expr
      | Some expr -> expr)
  | Ast.Const _ as expr -> expr
  | Ast.Annotated (expr, ty) -> Annotated (substitute_expression subst expr, ty)
  | Ast.Tuple exprs -> Tuple (List.map (substitute_expression subst) exprs)
  | Ast.Variant (label, expr) ->
      Variant (label, Option.map (substitute_expression subst) expr)
  | Ast.Lambda abs -> Lambda (substitute_abstraction subst abs)
  | Ast.RecLambda (x, abs) -> RecLambda (x, substitute_abstraction subst abs)
  | Ast.Fulfill expr -> Ast.Fulfill (substitute_expression subst expr)
  | Ast.Reference ref -> Ast.Reference ref
  | Ast.Boxed expr -> Ast.Boxed (substitute_expression subst expr)

and substitute_computation subst = function
  | Ast.Return expr -> Ast.Return (substitute_expression subst expr)
  | Ast.Do (comp, abs) ->
      Ast.Do
        (substitute_computation subst comp, substitute_abstraction subst abs)
  | Ast.Match (expr, cases) ->
      Ast.Match
        ( substitute_expression subst expr,
          List.map (substitute_abstraction subst) cases )
  | Ast.Apply (expr1, expr2) ->
      Ast.Apply
        (substitute_expression subst expr1, substitute_expression subst expr2)
  | Ast.Operation (Signal (op, expr), comp) ->
      Operation
        ( Signal (op, substitute_expression subst expr),
          substitute_computation subst comp )
  | Ast.Operation (Promise (k, op, abs, p), comp) ->
      let subst' = remove_pattern_bound_variables subst (PVar p) in
      Operation
        ( Promise (k, op, substitute_abstraction subst abs, p),
          substitute_computation subst' comp )
  | Ast.Operation (Spawn comp1, comp2) ->
      Operation
        ( Spawn (substitute_computation subst comp1),
          substitute_computation subst comp2 )
  | Ast.Interrupt (op, expr, comp) ->
      Interrupt
        (op, substitute_expression subst expr, substitute_computation subst comp)
  | Ast.Await (expr, abs) ->
      Await (substitute_expression subst expr, substitute_abstraction subst abs)
  | Ast.Unbox (expr, abs) ->
      Unbox (substitute_expression subst expr, substitute_abstraction subst abs)

and substitute_abstraction subst (pat, comp) =
  let subst' = remove_pattern_bound_variables subst pat in
  (pat, substitute_computation subst' comp)

let substitute subst comp =
  let subst = Ast.VariableMap.map (refresh_expression []) subst in
  substitute_computation subst comp

let rec eval_function env = function
  | Ast.Lambda (pat, comp) ->
      fun arg ->
        let subst = match_pattern_with_expression env pat arg in
        substitute subst comp
  | Ast.RecLambda (f, (pat, comp)) as expr ->
      fun arg ->
        let subst =
          match_pattern_with_expression env pat arg
          |> Ast.VariableMap.add f expr
        in
        substitute subst comp
  | Ast.Var x -> (
      match Ast.VariableMap.find_opt x env.variables with
      | Some expr -> eval_function env expr
      | None -> Ast.VariableMap.find x env.builtin_functions)
  | expr ->
      Error.runtime "Function expected but got %t" (Ast.print_expression expr)

let step_in_context step env redCtx ctx term =
  let terms' = step env term in
  List.map (fun (red, term') -> (redCtx red, fun () -> ctx (term' ()))) terms'

let rec step_computation env = function
  | Ast.Return _ -> []
  | Ast.Match (expr, cases) ->
      let rec find_case = function
        | (pat, comp) :: cases -> (
            match match_pattern_with_expression env pat expr with
            | subst ->
                [ (ComputationRedex Match, fun () -> substitute subst comp) ]
            | exception PatternMismatch -> find_case cases)
        | [] -> []
      in
      find_case cases
  | Ast.Apply (expr1, expr2) ->
      let f = eval_function env expr1 in
      [ (ComputationRedex ApplyFun, fun () -> f expr2) ]
  | Ast.Do (comp1, comp2) -> (
      let comps1' =
        step_in_context step_computation env
          (fun red -> DoCtx red)
          (fun comp1' -> Ast.Do (comp1', comp2))
          comp1
      in
      match comp1 with
      | Ast.Return expr ->
          let pat, comp2' = comp2 in
          let subst = match_pattern_with_expression env pat expr in
          (ComputationRedex DoReturn, fun () -> substitute subst comp2')
          :: comps1'
      | Ast.Operation (out, comp1') ->
          ( ComputationRedex DoSignal,
            fun () -> Operation (out, Ast.Do (comp1', comp2)) )
          :: comps1'
      | _ -> comps1')
  | Ast.Operation ((Ast.Promise (k, op, op_comp, p) as out), comp) -> (
      let comps' =
        step_in_context step_computation env
          (fun red -> SignalCtx red)
          (fun comp' -> Ast.Operation (out, comp'))
          comp
      in
      match comp with
      | Ast.Operation (Ast.Promise _, _) -> comps'
      | Ast.Operation (out, cont') ->
          ( ComputationRedex PromiseSignal,
            fun () ->
              Ast.Operation
                (out, Ast.Operation (Ast.Promise (k, op, op_comp, p), cont')) )
          :: comps'
      | _ -> comps')
  | Ast.Operation (out, comp) ->
      step_in_context step_computation env
        (fun red -> SignalCtx red)
        (fun comp' -> Ast.Operation (out, comp'))
        comp
  | Ast.Interrupt (op, expr, comp) -> (
      let comps' =
        step_in_context step_computation env
          (fun red -> InterruptCtx red)
          (fun comp' -> Ast.Interrupt (op, expr, comp'))
          comp
      in
      match comp with
      | Ast.Return expr ->
          (ComputationRedex InterruptReturn, fun () -> Ast.Return expr)
          :: comps'
      | Ast.Operation (out, comp) ->
          ( ComputationRedex InterruptSignal,
            fun () -> step_in_out env op expr comp out )
          :: comps'
      | _ -> comps')
  | Ast.Await (expr, (pat, comp)) -> (
      match expr with
      | Ast.Fulfill expr ->
          let subst = match_pattern_with_expression env pat expr in
          [ (ComputationRedex AwaitFulfill, fun () -> substitute subst comp) ]
      | _ -> [])
  | Ast.Unbox (expr, (pat, comp)) -> (
      match expr with
      | Ast.Boxed expr ->
          let subst = match_pattern_with_expression env pat expr in
          [ (ComputationRedex Unbox, fun () -> substitute subst comp) ]
      | Ast.Var x ->
          let expr' = Ast.VariableMap.find x env.variables in
          [ (ComputationRedex Unbox, fun () -> Ast.Unbox (expr', (pat, comp))) ]
      | _ ->
          Error.runtime "Expected boxed expresion but got %t instead."
            (Ast.print_expression expr))

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
        |> List.map (fun (red, comp') ->
               (RunCtx red, fun () -> Ast.Run (comp' ())))
      in
      match comp with
      | Ast.Operation (Ast.Signal (op, expr), comp') ->
          ( ProcessRedex RunSignal,
            fun () -> Ast.SignalProc (op, expr, Ast.Run comp') )
          :: comps'
      | Ast.Operation (Ast.Spawn comp1, comp2) ->
          ( ProcessRedex RunSpawn,
            fun () -> Ast.Parallel (Ast.Run comp1, Ast.Run comp2) )
          :: ( ProcessRedex RunSpawn,
               fun () -> Ast.Parallel (Ast.Run comp2, Ast.Run comp1) )
          :: comps'
      | _ -> comps')
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
              fun () ->
                Ast.SignalProc
                  ( op,
                    expr,
                    Ast.Parallel (proc1', Ast.InterruptProc (op, expr, proc2))
                  ) )
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
              fun () ->
                Ast.SignalProc
                  ( op,
                    expr,
                    Ast.Parallel (Ast.InterruptProc (op, expr, proc1), proc2')
                  ) )
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
          ( ProcessRedex InterruptRun,
            fun () -> Ast.Run (Ast.Interrupt (op, expr, comp)) )
          :: procs'
      | Ast.Parallel (proc1, proc2) ->
          ( ProcessRedex InterruptParallel,
            fun () ->
              Ast.Parallel
                ( Ast.InterruptProc (op, expr, proc1),
                  Ast.InterruptProc (op, expr, proc2) ) )
          :: procs'
      | Ast.SignalProc (op', expr', proc') ->
          ( ProcessRedex InterruptSignal,
            fun () ->
              Ast.SignalProc (op', expr', Ast.InterruptProc (op, expr, proc'))
          )
          :: procs'
      | _ -> procs')
  | Ast.SignalProc (op, expr, proc) ->
      step_in_context step_process state
        (fun red -> SignalProcCtx red)
        (fun proc' -> Ast.SignalProc (op, expr, proc'))
        proc

type load_state = {
  environment : environment;
  computations : Ast.computation list;
}

let initial_load_state =
  { environment = initial_environment; computations = [] }

let load_primitive load_state x prim =
  {
    load_state with
    environment =
      {
        load_state.environment with
        builtin_functions =
          Ast.VariableMap.add x
            (Primitives.primitive_function prim)
            load_state.environment.builtin_functions;
      };
  }

let load_ty_def load_state _ = load_state

let load_top_let load_state x expr =
  {
    load_state with
    environment =
      {
        load_state.environment with
        variables = Ast.VariableMap.add x expr load_state.environment.variables;
      };
  }

let load_top_do load_state comp =
  { load_state with computations = load_state.computations @ [ comp ] }

type sent_operation =
  | Interrupt of Ast.opsym * Ast.expression
  | Signal of Ast.opsym * Ast.expression

type run_state = {
  environment : environment;
  process : Ast.process;
  opsyms : Ast.opsym list;
  sent_operations : sent_operation list;
}

type step_label = ProcessReduction of process_reduction | Return | TopSignal
type step = { label : step_label; next_state : unit -> run_state }

let make_process = function
  | [] -> Ast.Run (Ast.Return (Ast.Tuple []))
  | comp :: comps ->
      List.fold_left
        (fun proc comp -> Ast.Parallel (proc, Ast.Run comp))
        (Ast.Run comp) comps

let incoming_operation state op expr =
  {
    state with
    process = Ast.InterruptProc (op, expr, state.process);
    sent_operations = Interrupt (op, expr) :: state.sent_operations;
  }

let run (load_state : load_state) =
  {
    environment = load_state.environment;
    process = make_process load_state.computations;
    sent_operations = [];
    opsyms = [];
  }

let steps state =
  let steps =
    step_process state.environment state.process
    |> List.map (fun (red, proc) ->
           {
             label = ProcessReduction red;
             next_state = (fun () -> { state with process = proc () });
           })
  in
  match state.process with
  | Ast.SignalProc (op, expr, proc) ->
      {
        label = TopSignal;
        next_state =
          (fun () ->
            {
              state with
              process = proc;
              sent_operations = Signal (op, expr) :: state.sent_operations;
            });
      }
      :: steps
  | _ -> steps
