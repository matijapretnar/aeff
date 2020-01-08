type state = {
    top_computations: Ast.computation list
}

let initial_state = {
    top_computations = []
}

let top_do state comp =
  {top_computations = comp :: state.top_computations}


let step_process interpreter_state state i =
    let comps =
        List.mapi (fun j comp -> if i = j then Interpreter.step interpreter_state comp else comp) state.top_computations
    in
    {top_computations=comps}

let incoming_operation interpreter_state state op comp indices =
    let expr = Interpreter.eval_expr interpreter_state comp in
    let comps =
        List.mapi (fun j comp -> if List.mem j indices then Ast.In (op, expr, comp) else comp) state.top_computations
    in
    {top_computations=comps}
