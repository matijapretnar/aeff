type state = 
  { variables: Ast.ty Ast.VariableMap.t;
    operations: Ast.ty Ast.OperationMap.t;
    type_definitions: (Ast.ty_param list * Ast.ty_def) Ast.TyNameMap.t }

let initial_state =
  { variables= Ast.VariableMap.empty;
    operations= Ast.OperationMap.empty;
    type_definitions=
        Ast.TyNameMap.empty
        |> Ast.TyNameMap.add Ast.bool_ty_name ([], Ast.TyInline (Ast.TyConst (Const.BooleanTy)))
        |> Ast.TyNameMap.add Ast.int_ty_name ([], Ast.TyInline (Ast.TyConst (Const.IntegerTy)))
        |> Ast.TyNameMap.add Ast.unit_ty_name ([], Ast.TyInline (Ast.TyTuple []))
        |> Ast.TyNameMap.add Ast.string_ty_name ([], Ast.TyInline (Ast.TyConst (Const.StringTy)))
        |> Ast.TyNameMap.add Ast.float_ty_name ([], Ast.TyInline (Ast.TyConst (Const.FloatTy)))
        (* |> Ast.TyNameMap.add Ast.list_ty_name ([], Ast.TyConst (Const.BooleanTy)) *)
        |> Ast.TyNameMap.add Ast.empty_ty_name ([], Ast.TySum [])
 }

let fresh_ty () =
    let a = Ast.TyParam.fresh "ty" in
    Ast.TyParam a

let extend_variables state vars =
    List.fold_left (fun state (x, ty) ->
    {state with variables = Ast.VariableMap.add x ty state.variables}) state vars

let rec infer_pattern state = function
  | Ast.PVar x ->
        let ty = fresh_ty () in
        ty, [(x, ty)], []
  | Ast.PAs (pat, x) ->
      let ty, vars, eqs = infer_pattern state pat in
      ty, (x, ty) :: vars, eqs
  | Ast.PConst c ->
        Ast.TyConst (Const.infer_ty c), [], []
  | Ast.PNonbinding -> 
        let ty = fresh_ty () in
        ty, [], []
  | Ast.PTuple pats ->
      let fold pat (tys, vars, eqs) =
        let ty', vars', eqs' = infer_pattern state pat in
        ty' :: tys, vars' @ vars, eqs' @ eqs
      in
      let tys, vars, eqs = List.fold_right fold pats ([], [], []) in
      Ast.TyTuple tys, vars, eqs

let rec infer_expression state = function
  | Ast.Var x ->
      Ast.VariableMap.find x state.variables, []
  | Ast.Const c ->
      Ast.TyConst (Const.infer_ty c), []
  | Ast.Annotated  (expr, ty) ->
      let ty', eqs = infer_expression state expr in
      ty, (ty, ty') :: eqs
  | Ast.Tuple exprs ->
      let fold expr (tys, eqs) =
          let ty', eqs' = infer_expression state expr in
          ty' :: tys, eqs' @ eqs
      in
      let tys, eqs = List.fold_right fold exprs ([], []) in
      Ast.TyTuple tys, eqs
  | Ast.Lambda abs ->
      let ty, ty', eqs = infer_abstraction state abs in
      Ast.TyArrow (ty, ty'), eqs
  | Ast.Fulfill expr ->
      let ty, eqs = infer_expression state expr in
      Ast.TyPromise ty, eqs
  | Ast.Reference expr_ref ->
      let ty, eqs = infer_expression state !expr_ref in
      Ast.TyReference ty, eqs
and infer_computation state = function
  | Ast.Return expr ->
      let ty, eqs = infer_expression state expr in
      ty, eqs
  | Ast.Do (comp1, comp2) ->
      let ty1, eqs1 = infer_computation state comp1 in
      let ty1', ty2, eqs2 = infer_abstraction state comp2 in
      ty2, (ty1, ty1') :: eqs1 @ eqs2
  | Ast.Apply (e1, e2) ->
      let t1, eqs1 = infer_expression state e1
      and t2, eqs2 = infer_expression state e2
      and a = fresh_ty ()
      in
      a, (t1, Ast.TyArrow (t2, a)) :: eqs1 @ eqs2
  | Ast.Out (op, expr, comp) | Ast.In (op, expr, comp) ->
      let ty1 = Ast.OperationMap.find op state.operations
      and ty2, eqs1 = infer_expression state expr
      and ty3, eqs2 = infer_computation state comp
      in
      ty3, (ty1, ty2) :: eqs1 @ eqs2
  | Ast.Await (e, abs) ->
      let pty1, eqs1 = infer_expression state e
      and ty1, ty2, eqs2 = infer_abstraction state abs
      in
      ty2, (pty1, Ast.TyPromise ty1) :: eqs1 @ eqs2
  | Ast.Match (e, cases) ->
      let ty1, eqs = infer_expression state e
      and ty2 = fresh_ty () in
      let fold eqs abs =
        let ty1', ty2', eqs' = infer_abstraction state abs in
        (ty1, ty1') :: (ty2, ty2') :: eqs' @ eqs
      in
      ty2, List.fold_left fold eqs cases
  | Ast.Handler (op, abs, p, comp) ->
      let ty1 = Ast.OperationMap.find op state.operations
      and ty1', ty2, eqs1 = infer_abstraction state abs
      and ty2' = Ast.TyPromise (fresh_ty ())
      in
      let state' = extend_variables state [(p, ty2')] in
      let ty, eqs2 = infer_computation state' comp in
      ty, (ty1, ty1') :: (ty2, ty2') :: eqs1 @ eqs2 
and infer_abstraction state (pat, comp) =
      let ty, vars, eqs = infer_pattern state pat in
      let state' = extend_variables state vars in
      let ty', eqs' = infer_computation state' comp in
      ty, ty', eqs @ eqs'

let subst_equations sbst =
  let subst_equation (t1, t2) = (Ast.substitute_ty sbst t1, Ast.substitute_ty sbst t2) in
  List.map subst_equation

let add_subst a t sbst = Ast.TyParamMap.add a (Ast.substitute_ty sbst t) sbst

let rec occurs a = function
  | Ast.TyParam a' -> a = a'
  | Ast.TyConst _ -> false
  | Ast.TyArrow (ty1, ty2) -> occurs a ty1 || occurs a ty2
  | Ast.TyApply (_, tys) -> List.exists (occurs a) tys
  | Ast.TyTuple tys -> List.exists (occurs a) tys
  | Ast.TyPromise ty -> occurs a ty
  | Ast.TyReference ty -> occurs a ty

let is_transparent_type state ty_name =
    match Ast.TyNameMap.find ty_name state.type_definitions with
    | (_, Ast.TySum _) -> false
    | (_, Ast.TyInline _) -> true

let unfold state ty_name args =
    match Ast.TyNameMap.find ty_name state.type_definitions with
    | (_, Ast.TySum _) -> assert false
    | (params, Ast.TyInline ty) -> ty

let rec unify state = function
  | [] -> Ast.TyParamMap.empty
  | (t1, t2) :: eqs when t1 = t2 ->
      unify state eqs
  | (Ast.TyApply (ty_name1, args1), Ast.TyApply (ty_name2, args2)) :: eqs when ty_name1 = ty_name2 ->
      unify state (List.combine args1 args2 @ eqs)      
  | (Ast.TyApply (ty_name, args), ty) :: eqs when is_transparent_type state ty_name ->
      unify state ((unfold state ty_name args, ty) :: eqs)
  | (ty, Ast.TyApply (ty_name, args)) :: eqs when is_transparent_type state ty_name ->
      unify state ((ty, unfold state ty_name args) :: eqs)
  | (Ast.TyTuple tys1, Ast.TyTuple tys2) :: eqs when List.length tys1 = List.length tys2 ->
      unify state (List.combine tys1 tys2 @ eqs)
  | (Ast.TyArrow (t1, t1'), Ast.TyArrow (t2, t2')) :: eqs ->
      unify state ((t1, t2) :: (t1', t2') :: eqs)
  | (Ast.TyPromise ty1, Ast.TyPromise ty2) :: eqs ->
      unify state ((ty1, ty2) :: eqs)
  | (Ast.TyReference ty1, Ast.TyReference ty2) :: eqs ->
      unify state ((ty1, ty2) :: eqs)
  | (Ast.TyParam a, t) :: eqs when not (occurs a t) ->
      add_subst a t (unify state (subst_equations (Ast.TyParamMap.singleton a t) eqs))
  | (t, Ast.TyParam a) :: eqs when not (occurs a t) ->
      add_subst a t (unify state (subst_equations (Ast.TyParamMap.singleton a t) eqs))
  | (t1, t2) :: _ ->
      Error.typing "Cannot unify %t = %t" (Ast.print_ty t1) (Ast.print_ty t2)

let infer state e =
  let t, eqs = infer_computation state e in
  let sbst = unify state eqs in
  let t' = Ast.substitute_ty sbst t in
  t'

let add_external_function x ty state =
  {state with variables = Ast.VariableMap.add x ty state.variables}

let add_operation state op ty =
  {state with operations = Ast.OperationMap.add op ty state.operations}

let add_top_definition state pat expr =
    let ty, vars, eqs = infer_pattern state pat
    and ty', eqs' = infer_expression state expr
    in
    let subst = unify state ((ty, ty') :: eqs @ eqs') in
    let vars' = List.map (fun (x, ty) -> (x, Ast.substitute_ty subst ty)) vars in
    extend_variables state vars'

let add_type_definitions state ty_defs =
    List.fold_left (fun state (params, ty_name, ty_def) ->
      {state with type_definitions = Ast.TyNameMap.add ty_name (params, ty_def) state.type_definitions}
    ) state ty_defs