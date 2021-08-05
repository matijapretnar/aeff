open Utils
module Ast = Language.Ast
module Const = Language.Const

type ty_scheme = Ast.ty_param list * Ast.ty

type state = {
  global_var : ty_scheme Ast.VariableMap.t;
  local_var : Ast.ty Ast.VariableMap.t list;
  operations : Ast.ty Ast.OpSymMap.t;
  type_definitions : (Ast.ty_param list * Ast.ty_def) Ast.TyNameMap.t;
}

type constraints = {
  equations : (Ast.ty * Ast.ty) list;
  mobile_types : Ast.ty list;
}

let initial_state =
  {
    global_var = Ast.VariableMap.empty;
    local_var = [ Ast.VariableMap.empty ];
    operations = Ast.OpSymMap.empty;
    type_definitions =
      ( Ast.TyNameMap.empty
      |> Ast.TyNameMap.add Ast.bool_ty_name
           ([], Ast.TyInline (Ast.TyConst Const.BooleanTy))
      |> Ast.TyNameMap.add Ast.int_ty_name
           ([], Ast.TyInline (Ast.TyConst Const.IntegerTy))
      |> Ast.TyNameMap.add Ast.unit_ty_name ([], Ast.TyInline (Ast.TyTuple []))
      |> Ast.TyNameMap.add Ast.string_ty_name
           ([], Ast.TyInline (Ast.TyConst Const.StringTy))
      |> Ast.TyNameMap.add Ast.float_ty_name
           ([], Ast.TyInline (Ast.TyConst Const.FloatTy))
      |> (let a = Ast.TyParam.fresh "ref" in
          Ast.TyNameMap.add Ast.ref_ty_name
            ([ a ], Ast.TyInline (Ast.TyReference (Ast.TyParam a))))
      |> Ast.TyNameMap.add Ast.empty_ty_name ([], Ast.TySum [])
      |>
      let a = Ast.TyParam.fresh "list" in
      Ast.TyNameMap.add Ast.list_ty_name
        ( [ a ],
          Ast.TySum
            [
              (Ast.nil_label, None);
              ( Ast.cons_label,
                Some
                  (Ast.TyTuple
                     [
                       Ast.TyParam a;
                       Ast.TyApply (Ast.list_ty_name, [ Ast.TyParam a ]);
                     ]) );
            ] ) );
  }

(* Previous versions would fail those two cases
   type foo 'a 'b = ['a] * 'b
   operation bar1 : <int> int foo = [<int>] * int // this one is  mobile, even though previous implementation would say no
   operation bar2 : int <int> foo = [int] * <int> // ok this one should fail. And it does :)

   type mobile_list 'm = | empty | something of ['m] * 'm list
   operation tasks : (unit -> int) mobile_list
*)

let rec is_mobile state candidates (ty : Ast.ty) : bool =
  match ty with
  | Ast.TyConst _ -> true
  | Ast.TyApply (ty_name, tys) -> is_apply_mobile state candidates ty_name tys
  | Ast.TyParam _ -> false
  | Ast.TyArrow _ -> false
  | Ast.TyTuple tys -> List.for_all (is_mobile state candidates) tys
  | Ast.TyPromise _ -> false
  | Ast.TyReference _ -> false
  | Ast.TyBoxed _ -> true

and is_apply_mobile state (candidates : (Ast.ty_name * bool list list) list)
    ty_name tys : bool =
  let are_tys_mobile = List.map (is_mobile state candidates) tys in
  (* int list is same as bool list. It doesnt matter which type exactly params becomes. only if its replaced by mobile or immobile type)  *)
  let seen_before_and_ok =
    match List.assoc_opt ty_name candidates with
    | Some options ->
        let rec check previous =
          match previous with
          | [] -> false
          | h :: t ->
              if
                List.for_all2
                  (fun p is_ty_mobile -> p = is_ty_mobile || is_ty_mobile)
                  h are_tys_mobile
              then true
              else check t
        in
        check options
    (* kinda like induction??? When we had fist met type we had to explore it.
       But now we can use IP and just check that it is exactly as in IP ??? *)
    (* We should eventually finish since there is limited combinations mobile/immobile types *)
    | None -> false
  in
  if seen_before_and_ok then true
  else
    let rec insert = function
      | [] -> [ (ty_name, [ are_tys_mobile ]) ]
      | (t, o) :: l when t = ty_name -> (t, are_tys_mobile :: o) :: l
      | h :: l -> h :: insert l
    in
    let candidates' = insert candidates in
    let params, ty_def = Ast.TyNameMap.find ty_name state.type_definitions in
    let subst =
      Ast.substitute_ty
        (List.combine params tys |> List.to_seq |> Ast.TyParamMap.of_seq)
    in
    match ty_def with
    | Ast.TyInline ty -> is_mobile state candidates' (subst ty)
    | Ast.TySum tys' ->
        let tys'' =
          List.fold_left
            (fun todo_tys (_lbl, ty) ->
              match ty with None -> todo_tys | Some ty -> ty :: todo_tys)
            [] tys'
        in
        List.for_all (is_mobile state candidates') (List.map subst tys'')

let fresh_ty () =
  let a = Ast.TyParam.fresh "ty" in
  Ast.TyParam a

let extend_variables state vars =
  match state.local_var with
  | [] -> assert false
  | head :: tail ->
      let head' =
        List.fold_left
          (fun state (x, ty) -> Ast.VariableMap.add x ty state)
          head vars
      in
      { state with local_var = head' :: tail }

let refreshing_subst params =
  List.fold_left
    (fun subst param ->
      let ty = fresh_ty () in
      Ast.TyParamMap.add param ty subst)
    Ast.TyParamMap.empty params

let infer_variant state lbl =
  let rec find = function
    | [] -> assert false
    | (_, (_, Ast.TyInline _)) :: ty_defs -> find ty_defs
    | (ty_name, (params, Ast.TySum variants)) :: ty_defs -> (
        match List.assoc_opt lbl variants with
        | None -> find ty_defs
        | Some ty -> (ty_name, params, ty) )
  in
  let ty_name, params, ty =
    find (Ast.TyNameMap.bindings state.type_definitions)
  in
  let subst = refreshing_subst params in
  let args = List.map (fun param -> Ast.TyParamMap.find param subst) params
  and ty' = Option.map (Ast.substitute_ty subst) ty in
  (ty', Ast.TyApply (ty_name, args))

let rec infer_pattern state = function
  | Ast.PVar x ->
      let ty = fresh_ty () in
      (ty, [ (x, ty) ], [])
  | Ast.PAs (pat, x) ->
      let ty, vars, eqs = infer_pattern state pat in
      (ty, (x, ty) :: vars, eqs)
  | Ast.PAnnotated (pat, ty) ->
      let ty', vars, eqs = infer_pattern state pat in
      (ty, vars, (ty, ty') :: eqs)
  | Ast.PConst c -> (Ast.TyConst (Const.infer_ty c), [], [])
  | Ast.PNonbinding ->
      let ty = fresh_ty () in
      (ty, [], [])
  | Ast.PTuple pats ->
      let fold pat (tys, vars, eqs) =
        let ty', vars', eqs' = infer_pattern state pat in
        (ty' :: tys, vars' @ vars, eqs' @ eqs)
      in
      let tys, vars, eqs = List.fold_right fold pats ([], [], []) in
      (Ast.TyTuple tys, vars, eqs)
  | Ast.PVariant (lbl, pat) -> (
      let ty_in, ty_out = infer_variant state lbl in
      match (ty_in, pat) with
      | None, None -> (ty_out, [], [])
      | Some ty_in, Some pat ->
          let ty, vars, eqs = infer_pattern state pat in
          (ty_out, vars, (ty_in, ty) :: eqs)
      | None, Some _ | Some _, None ->
          Error.typing "Variant optional argument mismatch" )

let infer_variable state x : Ast.ty * Ast.ty list =
  match Ast.VariableMap.find_opt x state.global_var with
  | Some (params, ty) ->
      let subst = refreshing_subst params in
      (Ast.substitute_ty subst ty, [])
  | None -> (
      match state.local_var with
      | [] -> assert false
      | head :: tail -> (
          match Ast.VariableMap.find_opt x head with
          | Some ty -> (ty, [])
          | None ->
              let rec find_movable local_var =
                match local_var with
                | [] -> assert false
                | h :: t -> (
                    match Ast.VariableMap.find_opt x h with
                    | Some ty -> ty
                    | None -> find_movable t )
              in
              let ty = find_movable tail in
              (ty, [ ty ]) ) )

let combine constraints1 constraints2 =
  {
    equations = constraints1.equations @ constraints2.equations;
    mobile_types = constraints1.mobile_types @ constraints2.mobile_types;
  }

let add_eqs constraints eqs =
  { constraints with equations = eqs @ constraints.equations }

let rec infer_expression state = function
  | Ast.Var x ->
      let ty, mobiles = infer_variable state x in
      (ty, { equations = []; mobile_types = mobiles })
  | Ast.Const c ->
      (Ast.TyConst (Const.infer_ty c), { equations = []; mobile_types = [] })
  | Ast.Annotated (expr, ty) ->
      let ty', constr = infer_expression state expr in
      (ty, add_eqs constr [ (ty, ty') ])
  | Ast.Tuple exprs ->
      let fold expr (tys, constr) =
        let ty', constr' = infer_expression state expr in
        (ty' :: tys, combine constr constr')
      in
      let tys, constr =
        List.fold_right fold exprs ([], { equations = []; mobile_types = [] })
      in
      (Ast.TyTuple tys, constr)
  | Ast.Lambda abs ->
      let ty, ty', constr = infer_abstraction state abs in
      (Ast.TyArrow (ty, ty'), constr)
  | Ast.RecLambda (f, abs) ->
      let f_ty = fresh_ty () in
      let state' = extend_variables state [ (f, f_ty) ] in
      let ty, ty', constr = infer_abstraction state' abs in
      let out_ty = Ast.TyArrow (ty, ty') in
      (out_ty, add_eqs constr [ (f_ty, out_ty) ])
  | Ast.Fulfill expr ->
      let ty, constr = infer_expression state expr in
      (Ast.TyPromise ty, constr)
  | Ast.Reference expr_ref ->
      let ty, constr = infer_expression state !expr_ref in
      (Ast.TyReference ty, constr)
  | Ast.Variant (lbl, expr) -> (
      let ty_in, ty_out = infer_variant state lbl in
      match (ty_in, expr) with
      | None, None -> (ty_out, { equations = []; mobile_types = [] })
      | Some ty_in, Some expr ->
          let ty, constr = infer_expression state expr in
          (ty_out, add_eqs constr [ (ty_in, ty) ])
      | None, Some _ | Some _, None ->
          Error.typing "Variant optional argument mismatch" )
  | Ast.Boxed expr ->
      let state' =
        { state with local_var = Ast.VariableMap.empty :: state.local_var }
      in
      let ty, constr = infer_expression state' expr in
      (Ast.TyBoxed ty, constr)

and infer_computation state = function
  | Ast.Return expr ->
      let ty, eqs = infer_expression state expr in
      (ty, eqs)
  | Ast.Do (comp1, comp2) ->
      let ty1, constr1 = infer_computation state comp1 in
      let ty1', ty2, constr2 = infer_abstraction state comp2 in
      (ty2, combine (add_eqs constr1 [ (ty1, ty1') ]) constr2)
  | Ast.Apply (e1, e2) ->
      let t1, constr1 = infer_expression state e1
      and t2, constr2 = infer_expression state e2
      and a = fresh_ty () in
      (a, combine (add_eqs constr1 [ (t1, Ast.TyArrow (t2, a)) ]) constr2)
  | Ast.Operation (Ast.Signal (op, expr), comp) | Ast.Interrupt (op, expr, comp)
    ->
      let ty1 = Ast.OpSymMap.find op state.operations
      and ty2, constr1 = infer_expression state expr
      and ty3, constr2 = infer_computation state comp in
      (ty3, combine (add_eqs constr1 [ (ty1, ty2) ]) constr2)
  | Ast.Await (e, abs) ->
      let pty1, constr1 = infer_expression state e
      and ty1, ty2, constr2 = infer_abstraction state abs in
      (ty2, combine (add_eqs constr1 [ (pty1, Ast.TyPromise ty1) ]) constr2)
  | Ast.Match (e, cases) ->
      let ty1, constr = infer_expression state e and ty2 = fresh_ty () in
      let fold constr abs =
        let ty1', ty2', constr' = infer_abstraction state abs in
        combine (add_eqs constr' [ (ty1, ty1'); (ty2, ty2') ]) constr
      in
      (ty2, List.fold_left fold constr cases)
  | Ast.Operation (Promise (k, op, abs, p), comp) ->
      let ty_k = fresh_ty () and ty_p = Ast.TyPromise (fresh_ty ()) in
      let ty1 = Ast.OpSymMap.find op state.operations in

      let state' =
        match k with
        | None -> state
        | Some k' -> extend_variables state [ (k', ty_k) ]
      in
      let ty1', ty2, constr1 = infer_abstraction state' abs in

      let state'' = extend_variables state [ (p, ty_p) ] in
      let ty, constr2 = infer_computation state'' comp in
      ( ty,
        combine
          (add_eqs constr1
             [
               (ty_k, Ast.TyArrow (Ast.TyTuple [], ty2));
               (ty1, ty1');
               (ty2, ty_p);
             ])
          constr2 )
  | Ast.Unbox (expr, abs) ->
      let ty, constr1 = infer_expression state expr in
      let ty' = fresh_ty () in
      let ty_boxed' = Ast.TyBoxed ty' in
      let ty1, ty2, constr2 = infer_abstraction state abs in
      (ty2, combine (add_eqs constr1 [ (ty, ty_boxed'); (ty', ty1) ]) constr2)
  | Ast.Operation (Ast.Spawn comp1, comp2) ->
      let state' =
        { state with local_var = Ast.VariableMap.empty :: state.local_var }
      in
      let ty1, constraints1 = infer_computation state' comp1 in
      let ty2, constraints2 = infer_computation state comp2 in
      ( ty2,
        add_eqs (combine constraints1 constraints2) [ (ty1, Ast.TyTuple []) ] )

and infer_abstraction state (pat, comp) =
  let ty, vars, eqs = infer_pattern state pat in
  let state' = extend_variables state vars in
  let ty', constr = infer_computation state' comp in
  (ty, ty', add_eqs constr eqs)

let subst_equations sbst =
  let subst_equation (t1, t2) =
    (Ast.substitute_ty sbst t1, Ast.substitute_ty sbst t2)
  in
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
  | Ast.TyBoxed ty -> occurs a ty

let is_transparent_type state ty_name =
  match Ast.TyNameMap.find ty_name state.type_definitions with
  | _, Ast.TySum _ -> false
  | _, Ast.TyInline _ -> true

let unfold state ty_name args =
  match Ast.TyNameMap.find ty_name state.type_definitions with
  | _, Ast.TySum _ -> assert false
  | params, Ast.TyInline ty ->
      let subst =
        List.combine params args |> List.to_seq |> Ast.TyParamMap.of_seq
      in
      Ast.substitute_ty subst ty

let rec unify state = function
  | [] -> Ast.TyParamMap.empty
  | (t1, t2) :: eqs when t1 = t2 -> unify state eqs
  | (Ast.TyApply (ty_name1, args1), Ast.TyApply (ty_name2, args2)) :: eqs
    when ty_name1 = ty_name2 ->
      unify state (List.combine args1 args2 @ eqs)
  | (Ast.TyApply (ty_name, args), ty) :: eqs
    when is_transparent_type state ty_name ->
      unify state ((unfold state ty_name args, ty) :: eqs)
  | (ty, Ast.TyApply (ty_name, args)) :: eqs
    when is_transparent_type state ty_name ->
      unify state ((ty, unfold state ty_name args) :: eqs)
  | (Ast.TyTuple tys1, Ast.TyTuple tys2) :: eqs
    when List.length tys1 = List.length tys2 ->
      unify state (List.combine tys1 tys2 @ eqs)
  | (Ast.TyArrow (t1, t1'), Ast.TyArrow (t2, t2')) :: eqs ->
      unify state ((t1, t2) :: (t1', t2') :: eqs)
  | (Ast.TyPromise ty1, Ast.TyPromise ty2) :: eqs ->
      unify state ((ty1, ty2) :: eqs)
  | (Ast.TyReference ty1, Ast.TyReference ty2) :: eqs ->
      unify state ((ty1, ty2) :: eqs)
  | (Ast.TyBoxed ty1, Ast.TyBoxed ty2) :: eqs -> unify state ((ty1, ty2) :: eqs)
  | (Ast.TyParam a, t) :: eqs when not (occurs a t) ->
      add_subst a t
        (unify state (subst_equations (Ast.TyParamMap.singleton a t) eqs))
  | (t, Ast.TyParam a) :: eqs when not (occurs a t) ->
      add_subst a t
        (unify state (subst_equations (Ast.TyParamMap.singleton a t) eqs))
  | (t1, t2) :: _ ->
      let print_param = Ast.new_print_param () in
      Error.typing "Cannot unify %t = %t"
        (Ast.print_ty print_param t1)
        (Ast.print_ty print_param t2)

let rec check_mobile state subst = function
  | [] -> ()
  | ty :: tys ->
      let ty' = Ast.substitute_ty subst ty in
      if is_mobile state [] ty' then check_mobile state subst tys
      else
        let pp = Ast.new_print_param () in
        Error.typing "Expected %t (originaly %t) to be mobile."
          (Ast.print_ty pp ty') (Ast.print_ty pp ty)

let infer state comp =
  let t, constr = infer_computation state comp in
  let sbst = unify state constr.equations in
  let t' = Ast.substitute_ty sbst t in
  check_mobile state sbst constr.mobile_types;
  t'

let add_external_function x ty_sch state =
  (* Format.printf "@[val %t : %t@]@." (Ast.Variable.print x)
     (Ast.print_ty_scheme ty_sch); *)
  { state with global_var = Ast.VariableMap.add x ty_sch state.global_var }

let load_primitive state x prim =
  let ty_sch = Primitives.primitive_type_scheme prim in
  add_external_function x ty_sch state

let add_operation state op ty =
  (* Format.printf "@[operation %t : %t@]@." (Ast.OpSym.print op)
     (Ast.print_ty_scheme ([], ty)); *)
  if is_mobile state [] ty then
    { state with operations = Ast.OpSymMap.add op ty state.operations }
  else Error.typing "Payload of an operation must be of a mobile type"

let add_top_definition state x expr =
  let ty, constr = infer_expression state expr in
  let subst = unify state constr.equations in
  let ty' = Ast.substitute_ty subst ty in
  check_mobile state subst constr.mobile_types;
  let free_vars = Ast.free_vars ty' |> Ast.TyParamSet.elements in
  let ty_sch = (free_vars, ty') in
  add_external_function x ty_sch state

let add_type_definitions state ty_defs =
  List.fold_left
    (fun state (params, ty_name, ty_def) ->
      (* Format.printf "@[type %t@]@." (Ast.TyName.print ty_name); *)
      {
        state with
        type_definitions =
          Ast.TyNameMap.add ty_name (params, ty_def) state.type_definitions;
      })
    state ty_defs

let check_payload state op expr =
  let ty1 = Ast.OpSymMap.find op state.operations
  and ty2, constr = infer_expression state expr in
  let subst = unify state (add_eqs constr [ (ty1, ty2) ]).equations in
  check_mobile state subst constr.mobile_types;
  subst
