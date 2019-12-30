type 'a located = {it: 'a; at: Location.t}

let add_loc ~loc it = {it = it; at = loc}

module StringMap = Map.Make(String)

type comparison = Less | Equal | Greater | Invalid

let fold = List.fold_left

let fold_map f s xs =
  let aux (s, reversed_ys) x =
    let s', y = f s x in
    (s', y :: reversed_ys)
  in
  let s', reversed_ys = fold aux (s, []) xs in
  (s', List.rev reversed_ys)

let rec left_to_right_map f = function
  | [] -> []
  | x :: xs ->
      let y = f x in
      let ys = left_to_right_map f xs in
      y :: ys

let concat_map f xs = List.concat (List.map f xs)

let unique_elements lst =
  let rec unique_elements acc = function
    | [] -> List.rev acc
    | x :: xs ->
        if List.mem x acc then unique_elements acc xs
        else unique_elements (x :: acc) xs
  in
  unique_elements [] lst

let no_duplicates lst =
  let rec check seen = function
    | [] -> true
    | x :: xs -> (not (List.mem x seen)) && check (x :: seen) xs
  in
  check [] lst

let list_diff lst1 lst2 = List.filter (fun x -> not (List.mem x lst2)) lst1

let option_map f = function None -> None | Some x -> Some (f x)

let map_default f default = function None -> default | Some x -> f x

let print ?(at_level = min_int) ?(max_level = max_int) ppf =
  if at_level <= max_level then Format.fprintf ppf
  else fun fmt -> Format.fprintf ppf ("(" ^^ fmt ^^ ")")

let rec print_sequence sep pp vs ppf =
  match vs with
  | [] -> ()
  | [v] -> pp v ppf
  | v :: vs -> Format.fprintf ppf "%t%s@,%t" (pp v) sep (print_sequence sep pp vs)

let rec print_cases pp vs ppf =
  match vs with
  | [] -> ()
  | [v] -> pp v ppf
  | v :: vs -> Format.fprintf ppf "%t@,| %t" (pp v) (print_cases pp vs)

let print_field fpp vpp (f, v) ppf = print ppf "%t = %t" (fpp f) (vpp v)

let print_tuple pp lst ppf =
  match lst with
  | [] -> print ppf "()"
  | lst -> print ppf "(@[<hov>%t@])" (print_sequence ", " pp lst)

let print_record fpp vpp assoc ppf =
  print ppf "{@[<hov>%t@]}" (print_sequence "; " (print_field fpp vpp) assoc)
