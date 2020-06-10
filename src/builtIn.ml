let binary_function f = function
  | Ast.Tuple [expr1; expr2] -> f expr1 expr2
  | expr -> Error.runtime "Pair expected but got %t" (Ast.print_expression expr)

let get_int = function
  | Ast.Const (Const.Integer n) -> n
  | expr -> Error.runtime "Integer expected but got %t" (Ast.print_expression expr)

let get_reference = function
  | Ast.Reference r -> r
  | expr -> Error.runtime "Reference expected but got %t" (Ast.print_expression expr)

let int_to f expr =
  let n = get_int expr in
  f n

let int_int_to f expr =
  binary_function (fun expr1 expr2 ->
    let n1 = get_int expr1 in
    let n2 = get_int expr2 in
    f n1 n2
  ) expr

let int_to_int name f =
  (name,
   ([], Ast.TyArrow (Ast.TyConst Const.IntegerTy, Ast.TyConst Const.IntegerTy)),
   int_to (fun n -> Ast.Return (Ast.Const (Const.Integer (f n)))))

let int_int_to_int name f =
  (name,
   ([], Ast.TyArrow (Ast.TyTuple [Ast.TyConst Const.IntegerTy; Ast.TyConst Const.IntegerTy], Ast.TyConst Const.IntegerTy)),
   int_int_to (fun n1 n2 -> Ast.Return (Ast.Const (Const.Integer (f n1 n2)))))

let poly_type ty =
  let a = Ast.TyParam.fresh "poly" in ([a], ty (Ast.TyParam a))

let poly_poly_to_bool name f =
  (name,
   (poly_type (fun a -> Ast.TyArrow (Ast.TyTuple [a; a], Ast.TyConst Const.BooleanTy))),
   binary_function (fun n1 n2 -> Ast.Return (Ast.Const (Const.Boolean (f n1 n2)))))

let functions = [
    poly_poly_to_bool "(=)" (=);
    poly_poly_to_bool "(<)" (<);
    poly_poly_to_bool "(>)" (>);
    poly_poly_to_bool "(<=)" (<=);
    poly_poly_to_bool "(>=)" (>=);
    poly_poly_to_bool "(<>)" (<>);
    int_to_int "(~-)" (~-);
    int_int_to_int "(+)" (+);
    int_int_to_int "(*)" ( * );
    int_int_to_int "(-)" (-);
    int_int_to_int "(mod)" (mod);
    int_int_to_int "(/)" (/);
    ("ref", poly_type (fun a -> Ast.TyArrow (a, Ast.TyReference a)), (fun v -> Ast.Return (Ast.Reference (ref v))));
    ("(!)", poly_type (fun a -> Ast.TyArrow (Ast.TyReference a, a)), (fun v -> let r = get_reference v in Ast.Return (!r)));
    ("(:=)", poly_type (fun a -> Ast.TyArrow (Ast.TyTuple [Ast.TyReference a; a], Ast.TyTuple [])), binary_function (fun v1 v2 -> let r = get_reference v1 in r := v2; Ast.Return (Ast.Tuple [])));
    ("toString", poly_type (fun a -> Ast.TyArrow (a, Ast.TyConst Const.StringTy)), (fun expr -> Ast.Return (Ast.Const (Const.String (Ast.string_of_expression expr)))))
] 
