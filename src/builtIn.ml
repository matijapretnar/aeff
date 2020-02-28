open Utils

let binary_function f = function
  | Ast.Tuple [expr1; expr2] -> f expr1 expr2
  | expr -> raise Interpreter.Stuck

let get_int = function
  | Ast.Const (Const.Integer n) -> n
  | expr -> raise Interpreter.Stuck

let get_reference = function
  | Ast.Reference r -> r
  | expr -> raise Interpreter.Stuck

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

let poly_poly_to_bool name f =
  let a = Ast.TyParam.fresh "poly" in
  (name,
   ([a], Ast.TyArrow (Ast.TyTuple [Ast.TyParam a; Ast.TyParam a], Ast.TyConst Const.BooleanTy)),
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
    (* ("ref", (fun v -> Ast.Return (Ast.Reference (ref v))));
    ("(!)", (fun v -> let r = get_reference v in Ast.Return (!r)));
    ("(:=)", binary_function (fun v1 v2 -> let r = get_reference v1 in r := v2; Ast.Return (Ast.Tuple []))) *)
] 
