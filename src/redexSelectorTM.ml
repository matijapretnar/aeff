let tag_marker = "###"

let rec print_computation ?max_level red c ppf =
  let print ?at_level = Utils.print ?max_level ?at_level ppf in
  let separator =
    match red with
    | Interpreter.Redex -> tag_marker
    | _ -> ""
  in
  print "%t%t%t"
    (fun ppf -> Format.pp_print_as ppf 0 separator)
    (print_computation' ?max_level red c)
    (fun ppf -> Format.pp_print_as ppf 0 separator)

and print_computation' ?max_level red c ppf =
  let print ?at_level = Utils.print ?max_level ?at_level ppf in
  match red, c with
  | (Interpreter.DoCtx red), Ast.Do (c1, (Ast.PNonbinding, c2)) ->
      print "@[<hov>%t;@ %t@]"
        (print_computation (red) c1)
        (Ast.print_computation c2)
  | (Interpreter.DoCtx red), Ast.Do (c1, (pat, c2)) ->
      print "@[<hov>let@[<hov>@ %t =@ %t@] in@ %t@]" (Ast.print_pattern pat)
        (print_computation (red) c1)
        (Ast.print_computation c2)
  | (Interpreter.InCtx red), Ast.In (op, e, c) ->
      print "↓%t(@[<hv>%t,@ %t@])" (Ast.Operation.print op)
        (Ast.print_expression e) (print_computation (red) c)
  | (Interpreter.OutCtx red), Ast.Out (op, e, c) ->
      print "↑%t(@[<hv>%t,@ %t@])" (Ast.Operation.print op)
        (Ast.print_expression e) (print_computation (red) c)
  | (Interpreter.PromiseCtx red), Ast.Handler (op, (p1, c1), p2, c2) ->
      print "@[<hv>promise (@[<hov>%t %t ↦@ %t@])@ as %t in@ %t@]"
        (Ast.Operation.print op) (Ast.print_pattern p1)
        (Ast.print_computation c1) (Ast.Variable.print p2)
        (print_computation (red) c2)
  | _, comp -> Ast.print_computation ?max_level comp ppf

let rec print_process ?max_level red proc ppf =
  let print ?at_level = Utils.print ?max_level ?at_level ppf in
  let separator =
    match red with
    | Runner.Redex -> tag_marker
    | _ -> ""
  in
  print "%t%t%t"
    (fun ppf -> Format.pp_print_as ppf 0 separator)
    (print_process' ?max_level red proc)
    (fun ppf -> Format.pp_print_as ppf 0 separator)

and print_process' ?max_level red proc ppf =
  let print ?at_level = Utils.print ?max_level ?at_level ppf in
  match red, proc with
  | (Runner.RunCtx red), Ast.Run comp ->
      print ~at_level:1 "run %t" (print_computation ~max_level:0 (red) comp)
  | (Runner.LeftCtx red), Ast.Parallel (proc1, proc2) ->
      print "@[<hv>%t@ || @ %t@]"
        (print_process (red) proc1)
        (Ast.print_process proc2)
  | (Runner.RightCtx red), Ast.Parallel (proc1, proc2) ->
      print "@[<hv>%t@ || @ %t@]"
        (Ast.print_process proc1)
        (print_process (red) proc2)
  | (Runner.InCtx red), Ast.InProc (op, expr, proc) ->
      print "↓%t(@[<hv>%t,@ %t@])" (Ast.Operation.print op)
        (Ast.print_expression expr)
        (print_process (red) proc)
  | (Runner.OutCtx red), Ast.OutProc (op, expr, proc) ->
      print "↑%t(@[<hv>%t,@ %t@])" (Ast.Operation.print op)
        (Ast.print_expression expr)
        (print_process (red) proc)
  | _, proc -> Ast.print_process ?max_level proc ppf

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

let view_process_with_redexes red proc =
    (match red with
    | None ->
        Ast.print_process proc Format.str_formatter
    | Some red ->
        print_process red proc Format.str_formatter
    );
    match split_string tag_marker (Format.flush_str_formatter ()) with
    | [code] -> [Vdom.text code]
    | [pre; redex; post] -> [Vdom.text pre; Vdom.elt "strong" ~a:[Vdom.class_ "has-text-info"] [Vdom.text redex]; Vdom.text post]
    | _ -> assert false
