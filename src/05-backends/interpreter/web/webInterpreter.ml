include Interpreter
open Vdom

type msg = HighlightRedex of bool
type model = { highlight_redex : bool }

let init = { highlight_redex = true }

let update_model _model = function
  | HighlightRedex show -> { highlight_redex = show }

let update_run_state run_state _msg = run_state

let view_model model =
  div
    ~a:[ class_ "panel" ]
    [
      elt "p" ~a:[ class_ "panel-heading" ] [ text "Options" ];
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
  div ~a:[ class_ "box" ] [ elt "pre" process_tree ]
