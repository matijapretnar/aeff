let rec match_computation_reduction red comp =
  match (red, comp) with
  | Interpreter.PromiseCtx red, Ast.Handler (_op, _op_comp, _p, comp) ->
      match_computation_reduction red comp
  | Interpreter.InCtx red, Ast.In (_op, _payload, comp) ->
      match_computation_reduction red comp
  | Interpreter.OutCtx red, Ast.Out (_op, _payload, comp) ->
      match_computation_reduction red comp
  | Interpreter.DoCtx red, Ast.Do (comp1, _comp2) ->
      match_computation_reduction red comp1
  | Interpreter.Redex, _comp -> true
  | _red, _comp -> false

let red match_process_reduction red proc =
  match (red, proc) with
  | Runner.LeftCtx red, Ast.Parallel (proc1, _proc2) ->
      match_process_reduction red proc1
  | Runner.RightCtx red, Ast.Parallel (_proc1, proc2) ->
      match_process_reduction red proc2
  | Runner.InCtx red, Ast.InProc (_op, _payload, proc) ->
      match_process_reduction red proc
  | Runner.OutCtx red, Ast.OutProc (_op, _payload, proc) ->
      match_process_reduction red proc
  | Runner.RunCtx red, Ast.Run comp -> match_computation_reduction red comp
  | Runner.Redex, _comp -> true
  | _red, _proc -> false

let tag_marker = "###"

let index_separator = "/"

let rec print_computation ?max_level reds c ppf =
  let print ?at_level = Utils.print ?max_level ?at_level ppf in
  let redex_indices =
    List.filter_map
      (function index, Interpreter.Redex -> Some index | _ -> None)
      reds
  in
  let separator =
    match redex_indices with
    | [] -> ""
    | _ ->
        Printf.sprintf "%s%s%s" tag_marker
          (String.concat index_separator (List.map string_of_int redex_indices))
          tag_marker
  in
  print "%t%t%t"
    (fun ppf -> Format.pp_print_as ppf 0 separator)
    (print_computation' ?max_level reds c)
    (fun ppf -> Format.pp_print_as ppf 0 separator)

and print_computation' ?max_level reds c ppf =
  let print ?at_level = Utils.print ?max_level ?at_level ppf in
  match c with
  | Ast.Do (c1, (Ast.PNonbinding, c2)) ->
      let reds =
        List.filter_map
          (function
            | index, Interpreter.DoCtx red -> Some (index, red) | _ -> None)
          reds
      in
      print "@[<hov>%t;@ %t@]"
        (print_computation reds c1)
        (Ast.print_computation c2)
  | Ast.Do (c1, (pat, c2)) ->
      let reds =
        List.filter_map
          (function
            | index, Interpreter.DoCtx red -> Some (index, red) | _ -> None)
          reds
      in
      print "@[<hov>let@[<hov>@ %t =@ %t@] in@ %t@]" (Ast.print_pattern pat)
        (print_computation reds c1)
        (Ast.print_computation c2)
  | Ast.In (op, e, c) ->
      let reds =
        List.filter_map
          (function
            | index, Interpreter.InCtx red -> Some (index, red) | _ -> None)
          reds
      in
      print "↓%t(@[<hv>%t,@ %t@])" (Ast.Operation.print op)
        (Ast.print_expression e) (print_computation reds c)
  | Ast.Out (op, e, c) ->
      let reds =
        List.filter_map
          (function
            | index, Interpreter.OutCtx red -> Some (index, red) | _ -> None)
          reds
      in
      print "↑%t(@[<hv>%t,@ %t@])" (Ast.Operation.print op)
        (Ast.print_expression e) (print_computation reds c)
  | Ast.Handler (op, (p1, c1), p2, c2) ->
      let reds =
        List.filter_map
          (function
            | index, Interpreter.PromiseCtx red -> Some (index, red) | _ -> None)
          reds
      in
      print "@[<hv>promise (@[<hov>%t %t ↦@ %t@])@ as %t in@ %t@]"
        (Ast.Operation.print op) (Ast.print_pattern p1)
        (Ast.print_computation c1) (Ast.Variable.print p2)
        (print_computation reds c2)
  | comp -> Ast.print_computation comp ppf

let rec print_process ?max_level reds proc ppf =
  let print ?at_level = Utils.print ?max_level ?at_level ppf in
  let redex_indices =
    List.filter_map
      (function index, Runner.Redex -> Some index | _ -> None)
      reds
  in
  let separator =
    match redex_indices with
    | [] -> ""
    | _ ->
        Printf.sprintf "%s%s%s" tag_marker
          (String.concat index_separator (List.map string_of_int redex_indices))
          tag_marker
  in
  print "%t%t%t"
    (fun ppf -> Format.pp_print_as ppf 0 separator)
    (print_process' ?max_level reds proc)
    (fun ppf -> Format.pp_print_as ppf 0 separator)

and print_process' ?max_level reds proc ppf =
  let print ?at_level = Utils.print ?max_level ?at_level ppf in
  match proc with
  | Ast.Run comp ->
      let reds =
        List.filter_map
          (function index, Runner.RunCtx red -> Some (index, red) | _ -> None)
          reds
      in
      print ~at_level:1 "run %t" (print_computation ~max_level:0 reds comp)
  | Ast.Parallel (proc1, proc2) ->
      let reds1 =
        List.filter_map
          (function
            | index, Runner.LeftCtx red -> Some (index, red) | _ -> None)
          reds
      and reds2 =
        List.filter_map
          (function
            | index, Runner.RightCtx red -> Some (index, red) | _ -> None)
          reds
      in
      print "@[<hv>%t@ || @ %t@]"
        (print_process reds1 proc1)
        (print_process reds2 proc2)
  | Ast.InProc (op, expr, proc) ->
      let reds =
        List.filter_map
          (function index, Runner.InCtx red -> Some (index, red) | _ -> None)
          reds
      in
      print "↓%t(@[<hv>%t,@ %t@])" (Ast.Operation.print op)
        (Ast.print_expression expr)
        (print_process reds proc)
  | Ast.OutProc (op, expr, proc) ->
      let reds =
        List.filter_map
          (function index, Runner.OutCtx red -> Some (index, red) | _ -> None)
          reds
      in
      print "↑%t(@[<hv>%t,@ %t@])" (Ast.Operation.print op)
        (Ast.print_expression expr)
        (print_process reds proc)

let split_string sep str =
  let sep_len = String.length sep and str_len = String.length str in
  let sub_start = ref 0 and sub_end = ref 0 and subs = ref [] in
  while !sub_end <= str_len - sep_len do
    if String.sub str !sub_end sep_len = sep then (
      subs := String.sub str !sub_start (!sub_end - !sub_start) :: !subs;
      sub_start := !sub_end + sep_len;
      sub_end := !sub_start )
    else incr sub_end
  done;
  if !sub_start <= str_len then
    subs := String.sub str !sub_start (str_len - !sub_start) :: !subs;
  List.rev !subs

type code_tag_code_list =
    | Code of string * tag_code_list
and tag_code_list =
    | Empty
    | Tag of string * Runner.top_step list * code_tag_code_list

let rec code_tag_code_of_split_code procs = function
    | [] -> assert false
    | code :: tag_code_list -> Code (code, tag_code_of_split_code procs tag_code_list)
and tag_code_of_split_code procs = function
    | [] -> Empty
    | tag :: code_tag_code_list ->
        let procs' = List.map (fun index -> List.nth procs (int_of_string index)) (split_string index_separator tag) in
        Tag (tag, procs', code_tag_code_of_split_code procs code_tag_code_list)

let convert_to_html procs marked_code =
    let rec find_until tag = function
    | Code (_code, Empty) -> assert false
    | Code (code, Tag (tag', _, code_tag_list)) when tag = tag' ->
        Code (code, Empty), code_tag_list
    | Code (code, Tag (tag', steps, code_tag_list)) ->
        let inside, remainder = find_until tag code_tag_list in
        Code (code, Tag (tag', steps, inside)), remainder
    in
    let code_tag_list = marked_code |> split_string tag_marker |> code_tag_code_of_split_code procs in
    let rec code_tag_code_html = function
    | Code (code, tag_code_list) -> Vdom.text code :: tag_code_html tag_code_list
    and tag_code_html = function
    | Empty -> []
    | Tag (tag, [step], code_tag_code_list) ->
        let inside, remainder = find_until tag code_tag_code_list in
        Vdom.elt "span" ~a:[Vdom.class_ "tag is-info"; Vdom.onclick (fun _ -> Model.Step step)] (code_tag_code_html inside) :: code_tag_code_html remainder
    | Tag (_, _, _code_tag_code_list) -> assert false
    in
    code_tag_code_html code_tag_list

let view_process_with_redexes steps proc =
  let indexed_reds = List.mapi (fun index (red, _step) -> (index, red)) steps in
  print_process indexed_reds proc Format.str_formatter;
  convert_to_html (List.map snd steps) (Format.flush_str_formatter ())
