include Interpreter
open Vdom

type msg =
  | HighlightRedex of bool
  | ChangeInterruptOperation of Ast.opsym
  | ParseInterruptPayload of string
  | SendInterrupt

type model = {
  highlight_redex : bool;
  interrupt_operation : Ast.opsym option;
  unparsed_interrupt_payload : string;
  parsed_interrupt_payload : (Ast.expression, string) result;
}

let init =
  {
    highlight_redex = true;
    interrupt_operation = None;
    unparsed_interrupt_payload = "";
    parsed_interrupt_payload = Error "";
  }

let update_model model = function
  | HighlightRedex show -> { model with highlight_redex = show }
  | ChangeInterruptOperation op -> { model with interrupt_operation = Some op }
  | ParseInterruptPayload input ->
      {
        model with
        unparsed_interrupt_payload = input;
        parsed_interrupt_payload = Error ("Can't parse " ^ input);
      }
  | SendInterrupt -> model

let update_run_state model run_state = function
  | SendInterrupt -> (
      match (model.interrupt_operation, model.parsed_interrupt_payload) with
      | Some op, Ok expr -> Interpreter.incoming_operation run_state op expr
      | _, _ -> run_state)
  | HighlightRedex _ | ChangeInterruptOperation _ | ParseInterruptPayload _ ->
      run_state

let panel ?(a = []) heading blocks =
  div ~a:(class_ "panel" :: a)
    (elt "p" ~a:[ class_ "panel-heading" ] [ text heading ] :: blocks)

let panel_block = div ~a:[ class_ "panel-block" ]
let nil = text ""

let select ?(a = []) empty_description msg describe_choice selected choices =
  let view_choice choice =
    elt "option"
      ~a:[ bool_prop "selected" (selected choice) ]
      [ text (describe_choice choice) ]
  in
  div ~a
    [
      elt "select"
        ~a:[ onchange_index (fun i -> msg (List.nth choices (i - 1))) ]
        (elt "option"
           ~a:
             [
               disabled true;
               bool_prop "selected"
                 (List.for_all (fun choice -> not (selected choice)) choices);
             ]
           [ text empty_description ]
        :: List.map view_choice choices);
    ]

let view_sent_operations ops =
  let view_operation op =
    (match op with
    | Interpreter.Interrupt (op, expr) ->
        Format.fprintf Format.str_formatter "↓ %t %t" (Ast.OpSym.print op)
          (Ast.print_expression expr)
    | Interpreter.Signal (op, expr) ->
        Format.fprintf Format.str_formatter "↑ %t %t" (Ast.OpSym.print op)
          (Ast.print_expression expr));
    elt "a" ~a:[ class_ "panel-block" ] [ text (Format.flush_str_formatter ()) ]
  in
  panel "History" (List.map view_operation ops)

let view_send_interrupt model opsyms =
  let warn_payload =
    model.unparsed_interrupt_payload <> ""
    && Result.is_error model.parsed_interrupt_payload
  in
  panel_block
    [
      div
        ~a:[ class_ "field" ]
        [
          div
            ~a:[ class_ "field has-addons" ]
            [
              div
                ~a:[ class_ "control is-expanded" ]
                [
                  select
                    ~a:[ class_ "select is-fullwidth" ]
                    "Interrupt"
                    (fun operation -> ChangeInterruptOperation operation)
                    Ast.string_of_operation
                    (fun operation ->
                      Some operation = model.interrupt_operation)
                    opsyms;
                ];
              elt "p"
                ~a:[ class_ "control" ]
                [
                  input
                    ~a:
                      [
                        class_
                          (if warn_payload then "input is-danger" else "input");
                        type_ "text";
                        oninput (fun input -> ParseInterruptPayload input);
                        str_prop "placeholder" "payload";
                        disabled (Option.is_none model.interrupt_operation);
                        value model.unparsed_interrupt_payload;
                      ]
                    [];
                ];
              div
                ~a:[ class_ "control" ]
                [
                  (let dis =
                     Option.is_none model.interrupt_operation
                     || Result.is_error model.parsed_interrupt_payload
                   in
                   elt "button"
                     ~a:
                       [
                         class_ "button is-info";
                         onclick (fun _ -> SendInterrupt);
                         disabled dis;
                       ]
                     [ text "↓" ]);
                ];
            ];
          (match model.parsed_interrupt_payload with
          | Error msg when warn_payload ->
              elt "p" ~a:[ class_ "help is-danger" ] [ text msg ]
          | _ -> nil);
        ];
    ]

let view_model model =
  panel "Options"
    [
      elt "label"
        ~a:[ class_ "panel-block" ]
        [
          input
            ~a:
              [
                type_ "checkbox";
                onchange_checked (fun show -> HighlightRedex show);
                bool_prop "checked" model.highlight_redex;
              ]
            [];
          text "Highlight redex";
        ];
    ]

let view_computation_redex = function
  | Interpreter.Match -> "match"
  | Interpreter.ApplyFun -> "applyFun"
  | Interpreter.DoReturn -> "doReturn"
  | Interpreter.PromiseSignal -> "promiseSignal"
  | Interpreter.InterruptReturn -> "interruptReturn"
  | Interpreter.InterruptSignal -> "interruptSignal"
  | Interpreter.InterruptPromise -> "interruptPromise"
  | Interpreter.InterruptPromise' -> "interruptPromise"
  | Interpreter.DoSignal -> "doSignal"
  | Interpreter.AwaitFulfill -> "awaitFulfill"
  | Interpreter.Unbox -> "unbox"
  | Interpreter.Spawn -> "spawn"

let rec view_computation_reduction = function
  | Interpreter.DoCtx red -> view_computation_reduction red
  | Interpreter.ComputationRedex redex -> view_computation_redex redex
  | Interpreter.InterruptCtx red -> view_computation_reduction red
  | Interpreter.SignalCtx red -> view_computation_reduction red

let view_process_redex = function
  | Interpreter.RunSignal -> "runSignal"
  | Interpreter.RunSpawn -> "runSpawn"
  | Interpreter.ParallelSignal1 -> "parallelSignal1"
  | Interpreter.ParallelSignal2 -> "parallelSignal2"
  | Interpreter.InterruptRun -> "interruptRun"
  | Interpreter.InterruptParallel -> "interruptParallel"
  | Interpreter.InterruptSignal -> "interruptSignal"

let rec view_process_reduction = function
  | Interpreter.LeftCtx red -> view_process_reduction red
  | Interpreter.RightCtx red -> view_process_reduction red
  | Interpreter.InterruptProcCtx red -> view_process_reduction red
  | Interpreter.SignalProcCtx red -> view_process_reduction red
  | Interpreter.RunCtx red -> view_computation_reduction red
  | Interpreter.ProcessRedex redex -> view_process_redex redex

let view_step_label = function
  | Interpreter.ProcessReduction reduction ->
      text (view_process_reduction reduction)
  | Interpreter.Return -> text "return"
  | Interpreter.TopSignal -> text "topSignal"

let view_run_state model (run_state : run_state) step_label =
  let reduction =
    match step_label with
    | Some (ProcessReduction red) -> Some red
    | Some Interpreter.Return -> None
    | Some Interpreter.TopSignal -> None
    | None -> None
  in

  let process_tree =
    RedexSelectorTM.view_process_with_redexes model.highlight_redex reduction
      run_state.process
  in

  div
    ~a:[ class_ "box" ]
    [
      elt "pre" process_tree;
      view_sent_operations run_state.sent_operations;
      view_send_interrupt model run_state.opsyms;
    ]
