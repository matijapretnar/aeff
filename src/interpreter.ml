open Utils

type state =
  { variables: Ast.expression Ast.VariableMap.t;
    builtin_functions: (Ast.expression -> Ast.computation) Ast.VariableMap.t }

let initial_state =
  { variables =
      Ast.VariableMap.empty;
    builtin_functions = Ast.VariableMap.empty;
  }


exception PatternMatchFailed

let rec eval_tuple state expr =
    match expr.it with
    | Ast.Tuple exprs -> exprs
    | Ast.Var x -> eval_tuple state (Ast.VariableMap.find x state.variables)
    | _ -> Error.runtime ~loc:expr.at "Tuple expected but got %t" (Ast.print_expression expr)

let rec eval_variant state expr =
    match expr.it with
    | Ast.Variant (lbl, expr) -> (lbl, expr)
    | Ast.Var x -> eval_variant state (Ast.VariableMap.find x state.variables)
    | _ -> Error.runtime ~loc:expr.at "Variant expected but got %t" (Ast.print_expression expr)

let rec eval_const state expr =
    match expr.it with
    | Ast.Const c -> c
    | Ast.Var x -> eval_const state (Ast.VariableMap.find x state.variables)
    | _ -> Error.runtime ~loc:expr.at "Const expected but got %t" (Ast.print_expression expr)

let rec match_pattern_with_expression state pat expr =
    match_plain_pattern_with_expression state pat.it expr
and match_plain_pattern_with_expression state pat expr =
    match pat with
    | Ast.PVar x -> Ast.VariableMap.singleton x expr
    | Ast.PAnnotated (pat, _) -> match_pattern_with_expression state pat expr
    | Ast.PAs (pat, x) ->
        let subst = match_pattern_with_expression state pat expr in
        Ast.VariableMap.add x expr subst
    | Ast.PTuple pats ->
        let exprs = eval_tuple state expr in
        List.fold_left2 (fun subst pat expr ->
            let subst' = match_pattern_with_expression state pat expr in
            Ast.VariableMap.union (fun _ _ _ -> assert false) subst subst'
        ) Ast.VariableMap.empty pats exprs
    | Ast.PVariant (label, pat) ->
        begin match pat, eval_variant state expr with
        | None, (label', None) when label = label' ->
            Ast.VariableMap.empty
        | Some pat, (label', Some expr) when label = label' ->
            match_pattern_with_expression state pat expr
        | _, _ -> raise PatternMatchFailed
        end
    | Ast.PConst c when Const.equal c (eval_const state expr) -> Ast.VariableMap.empty
    | Ast.PNonbinding ->  Ast.VariableMap.empty
    | _ -> raise PatternMatchFailed

let rec eval_function state expr =
    match expr.it with
    | Ast.Lambda (pat, comp) ->
        fun arg ->
            let subst = match_pattern_with_expression state pat arg in
            Ast.substitute_computation subst comp
    | Ast.RecLambda (f, (pat, comp)) ->
        fun arg ->
            let subst =
                match_pattern_with_expression state pat arg
                |> Ast.VariableMap.add f expr
            in
            Ast.substitute_computation subst comp
    | Ast.Var x ->
        begin match Ast.VariableMap.find_opt x state.variables with
        | Some expr -> eval_function state expr
        | None -> Ast.VariableMap.find x state.builtin_functions
        end
    | _ -> Error.runtime ~loc:expr.at "Function expected but got %t" (Ast.print_expression expr)

exception Stuck

let rec step state {it=comp; at=loc} =
    try
        add_loc ~loc (step_plain state ~loc comp)
    with
        Not_found -> raise Stuck
and step_plain state ~loc = function
    | Ast.Return _ -> raise Stuck
    | Ast.Out _ -> raise Stuck
    | Ast.Hook (op, hook, (pat, {it=Ast.Out (op', expr', cont')})) ->
        Ast.Out (op', expr', add_loc ~loc (Ast.Hook (op, hook, (pat, cont'))))
    | Ast.Hook (op, hook, abs) -> Ast.Hook (op, hook, step_abs state abs)
    | Ast.In (_, _, {it=Ast.Return expr}) -> Ast.Return expr
    | Ast.In (op, expr, {it=Ast.Out (op', expr', cont')}) ->
        Ast.Out (op', expr', add_loc ~loc (Ast.In(op, expr, cont')))
    | Ast.In (op, expr, {it=Ast.Hook (op', (arg_pat, hook), (pat, cont))}) when op = op' ->
        let subst = match_pattern_with_expression state arg_pat expr in
        Ast.Do (Ast.substitute_computation subst hook, (pat, add_loc ~loc (Ast.In (op, expr, cont))))
    | Ast.In (op, expr, {it=Ast.Hook (op', hook, (pat, cont))}) ->
        Ast.Hook (op', hook, (pat, add_loc ~loc (Ast.In (op, expr, cont))))
    | Ast.In (op, expr, comp) -> Ast.In (op, expr, step state comp)
    | Ast.Match (expr, cases) ->
        let rec find_case = function
        | (pat, comp) :: cases ->
            begin match match_pattern_with_expression state pat expr with
            | subst -> (Ast.substitute_computation subst comp).it
            | exception PatternMatchFailed -> find_case cases
            end
        | [] -> raise Stuck
        in
        find_case cases
    | Ast.Apply (expr1, expr2) ->
        let f = eval_function state expr1 in
        (f expr2).it
    | Ast.Do ({it=Ast.Return expr}, (pat, comp)) ->
        let subst = match_pattern_with_expression state pat expr in
        (Ast.substitute_computation subst comp).it
    | Ast.Do ({it=Ast.Out (op, expr, comp1)}, comp2) ->
        Ast.Out (op, expr, (add_loc ~loc (Ast.Do (comp1, comp2))))
    | Ast.Do ({it=Ast.Hook (op, hook, (pat, comp1))}, comp2) ->
        Ast.Hook (op, hook, (pat, add_loc ~loc (Ast.Do (comp1, comp2))))
    | Ast.Do (comp1, cont2) ->
        Ast.Do (step state comp1, cont2)
and step_abs state (pat, comp) =
    (pat, step state comp)

let rec eval_expr state = function
    | {it=Ast.Return expr} -> expr
    | comp -> eval_expr state (step state comp)

let eval_top_let state pat comp =
    let expr = eval_expr state comp in
    let subst = match_pattern_with_expression state pat expr in
    let variables' = Ast.VariableMap.union (fun _ _ _ -> assert false) subst state.variables in
    {state with variables=variables'}

let add_external_function x def state =
  {state with builtin_functions = Ast.VariableMap.add x def state.builtin_functions}

let add_operation x op state =
  {state with builtin_functions = Ast.VariableMap.add x (fun expr -> add_loc ~loc:expr.at (Ast.Out (op, expr, Ast.return (add_loc ~loc:expr.at (Ast.Tuple []))))) state.builtin_functions}