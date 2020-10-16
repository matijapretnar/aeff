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

type redex =
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

type reduction =
  | PromiseCtx of reduction
  | InCtx of reduction
  | OutCtx of reduction
  | DoCtx of reduction
  | Redex of redex

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

let rec step state = function
  | Ast.Return _ -> []
  | Ast.Out (op, expr, comp) ->
      step_in_context state
        (fun red -> OutCtx red)
        (fun comp' -> Ast.Out (op, expr, comp'))
        comp
  | Ast.Handler (op, op_comp, p, comp) -> (
      let comps' =
        step_in_context state
          (fun red -> PromiseCtx red)
          (fun comp' -> Ast.Handler (op, op_comp, p, comp'))
          comp
      in
      match comp with
      | Ast.Out (op', expr', cont') ->
          ( Redex PromiseOut,
            Ast.Out (op', expr', Ast.Handler (op, op_comp, p, cont')) )
          :: comps'
      | _ -> comps' )
  | Ast.In (op, expr, comp) -> (
      let comps' =
        step_in_context state
          (fun red -> InCtx red)
          (fun comp' -> Ast.In (op, expr, comp'))
          comp
      in
      match comp with
      | Ast.Return expr -> (Redex InReturn, Ast.Return expr) :: comps'
      | Ast.Out (op', expr', cont') ->
          (Redex InOut, Ast.Out (op', expr', Ast.In (op, expr, cont')))
          :: comps'
      | Ast.Handler (op', (arg_pat, op_comp), p, comp) when op = op' ->
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
          (Redex InPromise, comp') :: comps'
      | Ast.Handler (op', op_comp, p, comp) ->
          ( Redex InPromise',
            Ast.Handler (op', op_comp, p, Ast.In (op, expr, comp)) )
          :: comps'
      | _ -> comps' )
  | Ast.Match (expr, cases) ->
      let rec find_case = function
        | (pat, comp) :: cases -> (
            match match_pattern_with_expression state pat expr with
            | subst -> [ (Redex Match, substitute subst comp) ]
            | exception PatternMismatch -> find_case cases )
        | [] -> []
      in
      find_case cases
  | Ast.Apply (expr1, expr2) ->
      let f = eval_function state expr1 in
      [ (Redex ApplyFun, f expr2) ]
  | Ast.Do (comp1, comp2) -> (
      let comps1' =
        step_in_context state
          (fun red -> DoCtx red)
          (fun comp1' -> Ast.Do (comp1', comp2))
          comp1
      in
      match comp1 with
      | Ast.Return expr ->
          let pat, comp2' = comp2 in
          let subst = match_pattern_with_expression state pat expr in
          (Redex DoReturn, substitute subst comp2') :: comps1'
      | Ast.Out (op, expr, comp1) ->
          (Redex DoOut, Ast.Out (op, expr, Ast.Do (comp1, comp2))) :: comps1'
      | Ast.Handler (op, handler, pat, comp1) ->
          ( Redex DoPromise,
            Ast.Handler (op, handler, pat, Ast.Do (comp1, comp2)) )
          :: comps1'
      | _ -> comps1' )
  | Ast.Await (expr, (pat, comp)) -> (
      match expr with
      | Ast.Fulfill expr ->
          let subst = match_pattern_with_expression state pat expr in
          [ (Redex AwaitFulfill, substitute subst comp) ]
      | _ -> [] )

and step_in_context state redCtx ctx comp =
  let comps' = step state comp in
  List.map (fun (red, comp') -> (redCtx red, ctx comp')) comps'

let eval_top_let state x expr =
  { state with variables = Ast.VariableMap.add x expr state.variables }

let add_external_function x def state =
  {
    state with
    builtin_functions = Ast.VariableMap.add x def state.builtin_functions;
  }
