open Utils
module Ast = Core.Ast
module Interpreter = Core.Interpreter

let tag_marker = "###"
let print_mark ppf = Format.pp_print_as ppf 0 tag_marker

let print_computation_redex ?max_level red c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match (red, c) with
  | (Interpreter.DoReturn | Interpreter.DoSignal), Ast.Do (c1, (pat, c2)) ->
      print "@[<hov>%tlet@[<hov>@ %t =@ %t@]%t in@ %t@]" print_mark
        (Ast.print_pattern pat) (Ast.print_computation c1) print_mark
        (Ast.print_computation c2)
  | _, comp ->
      print "%t%t%t" print_mark
        (fun ppf -> Ast.print_computation ?max_level comp ppf)
        print_mark

let rec print_computation_reduction ?max_level red c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match (red, c) with
  | Interpreter.DoCtx red, Ast.Do (c1, (Ast.PNonbinding, c2)) ->
      print "@[<hov>%t;@ %t@]"
        (print_computation_reduction red c1)
        (Ast.print_computation c2)
  | Interpreter.DoCtx red, Ast.Do (c1, (pat, c2)) ->
      print "@[<hov>let@[<hov>@ %t =@ %t@] in@ %t@]" (Ast.print_pattern pat)
        (print_computation_reduction red c1)
        (Ast.print_computation c2)
  | Interpreter.InterruptCtx red, Ast.Interrupt (op, e, c) ->
      print "↓%t(@[<hv>%t,@ %t@])" (Ast.OpSym.print op) (Ast.print_expression e)
        (print_computation_reduction red c)
  | Interpreter.SignalCtx red, Ast.Operation (Ast.Signal (op, e), c) ->
      print "↑%t(@[<hv>%t,@ %t@])" (Ast.OpSym.print op) (Ast.print_expression e)
        (print_computation_reduction red c)
  | ( Interpreter.SignalCtx red,
      Ast.Operation
        ( InterruptHandler
            {
              operation = op;
              handler =
                {
                  payload_pattern = p1;
                  resumption_pattern = r;
                  state_pattern = s;
                  body = c1;
                };
              state_value = v;
              promise = p2;
            },
          c2 ) ) ->
      print "@[<hv>promise (@[<hov>%t %t %t %t ↦@ %t@])@ %@ %t as %t in@ %t@]"
        (Ast.OpSym.print op) (Ast.print_pattern p1) (Ast.print_pattern r)
        (Ast.print_pattern s) (Ast.print_computation c1)
        (Ast.print_expression v) (Ast.Variable.print p2)
        (print_computation_reduction red c2)
  | Interpreter.ComputationRedex redex, c ->
      print_computation_redex ?max_level redex c ppf
  | _, _ -> assert false

let print_process_redex ?max_level _redex proc ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  print "%t%t%t" print_mark (Ast.print_process ?max_level proc) print_mark

let rec print_process_reduction ?max_level red proc ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match (red, proc) with
  | Interpreter.RunCtx red, Ast.Run comp ->
      print ~at_level:1 "run %t"
        (print_computation_reduction ~max_level:0 red comp)
  | Interpreter.LeftCtx red, Ast.Parallel (proc1, proc2) ->
      print "@[<hv>%t@ || @ %t@]"
        (print_process_reduction red proc1)
        (Ast.print_process proc2)
  | Interpreter.RightCtx red, Ast.Parallel (proc1, proc2) ->
      print "@[<hv>%t@ || @ %t@]" (Ast.print_process proc1)
        (print_process_reduction red proc2)
  | Interpreter.InterruptProcCtx red, Ast.InterruptProc (op, expr, proc) ->
      print "↓%t(@[<hv>%t,@ %t@])" (Ast.OpSym.print op)
        (Ast.print_expression expr)
        (print_process_reduction red proc)
  | Interpreter.SignalProcCtx red, Ast.SignalProc (op, expr, proc) ->
      print "↑%t(@[<hv>%t,@ %t@])" (Ast.OpSym.print op)
        (Ast.print_expression expr)
        (print_process_reduction red proc)
  | Interpreter.ProcessRedex redex, proc ->
      print_process_redex ?max_level redex proc ppf
  | _, _ -> assert false

let split_string sep str =
  let sep_len = String.length sep and str_len = String.length str in
  let sub_start = ref 0 and sub_end = ref 0 and subs = ref [] in
  while !sub_end <= str_len - sep_len do
    if String.sub str !sub_end sep_len = sep then (
      subs := String.sub str !sub_start (!sub_end - !sub_start) :: !subs;
      sub_start := !sub_end + sep_len;
      sub_end := !sub_start)
    else incr sub_end
  done;
  if !sub_start <= str_len then
    subs := String.sub str !sub_start (str_len - !sub_start) :: !subs;
  List.rev !subs

let view_process_with_redexes red proc =
  (match red with
  | None -> Ast.print_process proc Format.str_formatter
  | Some red -> print_process_reduction red proc Format.str_formatter);
  match split_string tag_marker (Format.flush_str_formatter ()) with
  | [ code ] -> [ Vdom.text code ]
  | [ pre; redex; post ] ->
      [
        Vdom.text pre;
        Vdom.elt "strong" ~a:[ Vdom.class_ "has-text-info" ] [ Vdom.text redex ];
        Vdom.text post;
      ]
  | _ -> assert false
