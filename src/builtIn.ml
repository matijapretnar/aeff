open Utils

let binary_function f = function
  | Ast.Tuple [expr1; expr2] -> f expr1 expr2
  | expr -> Error.runtime "A pair expected but got %t." (Ast.print_expression expr)

let get_int = function
  | Ast.Const (Const.Integer n) -> n
  | expr -> Error.runtime "An integer expected but got %t." (Ast.print_expression expr)

let int_to f expr =
  let n = get_int expr in
  f n

let int_int_to f expr =
  binary_function (fun expr1 expr2 ->
    let n1 = get_int expr1 in
    let n2 = get_int expr2 in
    f n1 n2
  ) expr

let int_to_int f expr =
  int_to (fun n -> Ast.Return (Ast.Const (Const.Integer (f n)))) expr

let int_int_to_int f expr =
  int_int_to (fun n1 n2 -> Ast.Return (Ast.Const (Const.Integer (f n1 n2)))) expr
let int_int_to_bool f expr =
  int_int_to (fun n1 n2 -> Ast.Return (Ast.Const (Const.Boolean (f n1 n2)))) expr

let functions = [
    ("(=)", int_int_to_bool (=));
    ("(<)", int_int_to_bool (<));
    ("(~-)", int_to_int (~-));
    ("(+)", int_int_to_int (+));
    ("(*)", int_int_to_int ( * ));
    ("(-)", int_int_to_int (-));
    ("(mod)", int_int_to_int (mod));
    ("(/)", int_int_to_int (/))
] 
