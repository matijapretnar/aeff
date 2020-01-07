open Utils

module TyName = Symbol.Make ()
type ty_name = TyName.t


let bool_ty_name = TyName.fresh "bool"

let int_ty_name = TyName.fresh "int"

let unit_ty_name = TyName.fresh "unit"

let string_ty_name = TyName.fresh "string"

let float_ty_name = TyName.fresh "float"

let list_ty_name = TyName.fresh "list"

let empty_ty_name = TyName.fresh "empty"


module TyParam = Symbol.Make ()
type ty_param = TyParam.t

type ty =
  | TyApply of ty_name * ty list  (** [(ty1, ty2, ..., tyn) type_name] *)
  | TyParam of ty_param  (** ['a] *)
  | TyArrow of ty * ty  (** [ty1 -> ty2] *)
  | TyTuple of ty list  (** [ty1 * ty2 * ... * tyn] *)

module Variable = Symbol.Make ()
module Label = Symbol.Make ()
module Operation = Symbol.Make ()
type variable = Variable.t
type label = Label.t
type operation = Operation.t

let nil_label = Label.fresh Syntax.nil_label
let cons_label = Label.fresh Syntax.cons_label

type pattern =
  | PVar of variable
  | PAnnotated of pattern * ty
  | PAs of pattern * variable
  | PTuple of pattern list
  | PVariant of label * pattern option
  | PConst of Const.t
  | PNonbinding

type expression =
  | Var of variable
  | Const of Const.t
  | Annotated of expression * ty
  | Tuple of expression list
  | Variant of label * expression option
  | Lambda of abstraction
  | RecLambda of variable * abstraction

and computation =
  | Return of expression
  | Do of computation * abstraction
  | Match of expression * abstraction list
  | Apply of expression * expression
  | Out of operation * expression * computation
  | In of operation * expression * computation
  | Hook of operation * abstraction * abstraction

and abstraction = pattern * computation

module VariableMap = Map.Make(Variable)

let rec remove_pattern_bound_variables subst = function
  | PVar x -> VariableMap.remove x subst
  | PAnnotated (pat, _) -> remove_pattern_bound_variables subst pat
  | PAs (pat, x) ->
      let subst = remove_pattern_bound_variables subst pat in
      VariableMap.remove x subst
  | PTuple pats ->
      List.fold_left remove_pattern_bound_variables subst pats
  | PVariant (_, None) -> subst
  | PVariant (_, Some pat) -> remove_pattern_bound_variables subst pat
  | PConst c -> subst
  | PNonbinding -> subst

let rec substitute_expression subst = function
  | Var x as expr ->
      begin match VariableMap.find_opt x subst with
      | None -> expr
      | Some expr -> expr
      end
  | Const _ as expr -> expr
  | Annotated (expr, ty) -> Annotated (substitute_expression subst expr, ty)
  | Tuple exprs -> Tuple (List.map (substitute_expression subst) exprs)
  | Variant (label, expr) -> Variant (label, Option.map (substitute_expression subst) expr)
  | Lambda abs -> Lambda (substitute_abstraction subst abs)
  | RecLambda (x, abs) -> RecLambda (x, substitute_abstraction subst abs)
and substitute_computation subst = function
  | Return expr -> Return (substitute_expression subst expr)
  | Do (comp, abs) -> Do (substitute_computation subst comp, substitute_abstraction subst abs)
  | Match (expr, cases) -> Match (substitute_expression subst expr, List.map (substitute_abstraction subst) cases)
  | Apply (expr1, expr2) -> Apply (substitute_expression subst expr1, substitute_expression subst expr2)
  | Out (op, expr, comp) -> Out (op, substitute_expression subst expr, substitute_computation subst comp)
  | In (op, expr, comp) -> In (op, substitute_expression subst expr, substitute_computation subst comp)
  | Hook (op, abs1, abs2) -> Hook (op, substitute_abstraction subst abs1, substitute_abstraction subst abs2)
and substitute_abstraction subst (pat, comp) =
  let subst' = remove_pattern_bound_variables subst pat in
  (pat, substitute_computation subst' comp)

type ty_def =
  | TySum of (label * ty option) list
  | TyInline of ty

type command =
  | TyDef of (ty_param list * ty_name * ty_def) list
  | Operation of variable * operation
  | TopLet of pattern * computation
  | TopDo of computation list


let rec print_pattern ?max_level p ppf =
  let print ?at_level = Utils.print ?max_level ?at_level ppf in
  match p with
  | PVar x -> print "%t" (Variable.print x)
  | PAs (p, x) ->
      print "%t as %t" (print_pattern p) (Variable.print x)
  | PAnnotated (p, ty) -> print_pattern ?max_level p ppf
  | PConst c -> Const.print c ppf
  | PTuple lst -> Utils.print_tuple print_pattern lst ppf
  | PVariant (lbl, None) when lbl = nil_label -> print "[]"
  | PVariant (lbl, None) -> print "%t" (Label.print lbl)
  | PVariant (lbl, Some (PTuple [v1; v2])) when lbl = cons_label ->
      print "%t::%t" (print_pattern v1) (print_pattern v2)
  | PVariant (lbl, Some p) ->
      print ~at_level:1 "%t @[<hov>%t@]"
        (Label.print lbl)
        (print_pattern p)
  | PNonbinding -> print "_"

let rec print_expression ?max_level e ppf =
  let print ?at_level = Utils.print ?max_level ?at_level ppf in
  match e with
  | Var x -> print "%t" (Variable.print x)
  | Const c -> print "%t" (Const.print c)
  | Annotated (t, ty) -> print_expression ?max_level t ppf
  | Tuple lst -> Utils.print_tuple print_expression lst ppf
  | Variant (lbl, None) when lbl = nil_label -> print "[]"
  | Variant (lbl, None) -> print "%t" (Label.print lbl)
  | Variant (lbl, Some (Tuple [v1; v2])) when lbl = cons_label ->
      print ~at_level:1 "%t::%t" (print_expression ~max_level:0 v1) (print_expression ~max_level:1 v2)
  | Variant (lbl, Some e) ->
      print ~at_level:1 "%t @[<hov>%t@]"
        (Label.print lbl)
        (print_expression ~max_level:0 e)
  | Lambda a -> print ~at_level:2 "fun %t" (print_abstraction a)
  | RecLambda (f, a) -> print ~at_level:2 "rec %t ..." (Variable.print f)

and print_computation ?max_level c ppf =
  let print ?at_level = Utils.print ?max_level ?at_level ppf in
  match c with
  | Return e -> print ~at_level:1 "return %t" (print_expression ~max_level:0 e)
  | Do (c1, (PNonbinding, c2)) ->
      print "@[<hov>%t;@ %t@]"
        (print_computation c1)
        (print_computation c2)
  | Do (c1, (pat, c2)) ->
      print "@[<hov>do@[<hov>@ %t ←@ %t@] in@ %t@]"
        (print_pattern pat)
        (print_computation c1)
        (print_computation c2)
  | Match (e, lst) ->
      print "match %t with (@[<hov>%t@])" (print_expression e)
        (Utils.print_sequence " | " case lst)
  | Apply (e1, e2) ->
      print ~at_level:1 "@[%t@ %t@]" (print_expression ~max_level:1 e1)
        (print_expression ~max_level:0 e2)
  | In (op, e, c) ->
      print "↓%t(@[<hv>%t;@ %t@])"
        (Operation.print op)
        (print_expression e)
        (print_computation c)
  | Out (op, e, c) ->
      print "↑%t(@[<hv>%t;@ %t@])"
        (Operation.print op)
        (print_expression e)
        (print_computation c)
  | Hook (op, (p1, c1), (p2, c2)) ->
      print "@[<hv>with@[<hov> %t %t →@ %t@]@ as %t in@ %t@]"
        (Operation.print op)
        (print_pattern p1)
        (print_computation c1)
        (print_pattern p2)
        (print_computation c2)

and print_abstraction (p, c) ppf =
  Format.fprintf ppf "%t → %t" (print_pattern p) (print_computation c)

and let_abstraction (p, c) ppf =
  Format.fprintf ppf "%t = %t" (print_pattern p) (print_computation c)

and case a ppf = Format.fprintf ppf "%t" (print_abstraction a)
