open Shared
open Vdom

let panel ?(a = []) heading blocks =
  div ~a:(class_ "panel" :: a)
    (elt "p" ~a:[ class_ "panel-heading" ] [ text heading ] :: blocks)

let panel_block = div ~a:[ class_ "panel-block" ]

let button txt msg =
  input [] ~a:[ onclick (fun _ -> msg); type_button; value txt ]

let disabled_button txt = input [] ~a:[ type_button; value txt; disabled true ]

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
        ( elt "option"
            ~a:
              [
                disabled true;
                bool_prop "selected"
                  (List.for_all (fun choice -> not (selected choice)) choices);
              ]
            [ text empty_description ]
        :: List.map view_choice choices );
    ]

let nil = text ""

let view_computation_redex = function
  | Interpreter.PromiseOut -> "promiseOut"
  | Interpreter.InReturn -> "inReturn"
  | Interpreter.InOut -> "inOut"
  | Interpreter.InPromise -> "inPromise"
  | Interpreter.InPromise' -> "inPromise"
  | Interpreter.Match -> "match"
  | Interpreter.ApplyFun -> "applyFun"
  | Interpreter.DoReturn -> "doReturn"
  | Interpreter.DoOut -> "doOut"
  | Interpreter.DoPromise -> "doPromise"
  | Interpreter.AwaitFulfill -> "awaitFulfill"

let rec view_computation_reduction = function
  | Interpreter.PromiseCtx red -> view_computation_reduction red
  | Interpreter.InCtx red -> view_computation_reduction red
  | Interpreter.OutCtx red -> view_computation_reduction red
  | Interpreter.DoCtx red -> view_computation_reduction red
  | Interpreter.Redex redex -> view_computation_redex redex

let view_process_redex = function
  | Runner.RunOut -> "runOut"
  | Runner.ParallelOut1 -> "parallelOut1"
  | Runner.ParallelOut2 -> "parallelOut2"
  | Runner.InRun -> "inRun"
  | Runner.InParallel -> "inParallel"
  | Runner.InOut -> "inOut"
  | Runner.TopOut -> "topOut"

let rec view_process_reduction = function
  | Runner.LeftCtx red -> view_process_reduction red
  | Runner.RightCtx red -> view_process_reduction red
  | Runner.InCtx red -> view_process_reduction red
  | Runner.OutCtx red -> view_process_reduction red
  | Runner.RunCtx red -> view_computation_reduction red
  | Runner.Redex redex -> view_process_redex redex

let step_action (red, step) =
  elt "li" [ button (view_process_reduction red) (Model.Step step) ]

(* let view_actions (model : Model.model) code =
  let _step_actions = List.map step_action (Model.steps code) in
  let random_action =
      valid_button
          ~input_placeholder:"Number of random steps to make"
          ~input_value:model.unparsed_step_size
          ~input_msg:(fun input -> Model.ChangeStepSize input)
          ~submit_msg:(fun _ -> Model.RandomStep)
          ~submit_value:"Step randomly"
          model.random_step_size
  and _back_action =
      match code.history with
      | [] -> disabled_button "back"
      | _ -> button "back" Model.Back
  and _interrupt_action =
      valid_button
          ~input_placeholder:"Interrupt, eg. \"op 10\""
          ~input_value:model.unparsed_interrupt
          ~input_msg:(fun input -> Model.ParseInterrupt input)
          ~submit_msg:(fun _ -> Model.Interrupt)
          ~submit_value:"interrupt"
          model.parsed_interrupt
  in
    elt "nav" ~a:[class_ "level"] [
      div ~a:[class_ "level-left"] [
        div ~a:[class_ "level-item"] [
          elt "button" ~a:[class_ "button is-danger"] [text "back"]
        ]
      ];
      div ~a:[class_ "level-right"] [
        random_action
      ]
    ]
    elt "ol" (back_action ::  :: step_actions @ [interrupt_action]) *)

let view_steps (model : Model.model) (code : Model.loaded_code) steps =
  let view_undo_last_step =
    panel_block
      [
        elt "button"
          ~a:
            [
              class_ "button is-outlined is-fullwidth is-small";
              onclick (fun _ -> Model.Back);
              disabled (code.history = []);
            ]
          [ text "Undo last step" ];
      ]
  and view_step i (red, step) =
    panel_block
      [
        elt "button"
          ~a:
            [
              class_ "button is-outlined is-fullwidth";
              onclick (fun _ -> Model.Step step);
              onmousemove (fun _ -> Model.SelectReduction (Some i));
            ]
          [ text (view_process_reduction red) ];
      ]
  and view_random_steps steps =
    div
      ~a:[ class_ "panel-block"; style "display" "block" ]
      [
        div
          ~a:[ class_ "field has-addons" ]
          [
            div
              ~a:[ class_ "control is-expanded" ]
              [
                select
                  ~a:[ class_ "select is-fullwidth is-info" ]
                  "Step size"
                  (fun step_size -> Model.ChangeRandomStepSize step_size)
                  string_of_int
                  (fun step_size -> step_size = model.random_step_size)
                  [ 1; 2; 4; 8; 16; 32; 64; 128; 256; 512; 1024 ];
              ];
            div ~a:[ class_ "control" ]
              [
                elt "button"
                  ~a:
                    [
                      class_ "button is-info";
                      onclick (fun _ -> Model.RandomStep);
                      disabled (steps = []);
                    ]
                  [ text "random steps" ];
              ];
          ];
        ( if steps = [] then
          elt "p" ~a:[ class_ "help" ]
            [
              text "Computation has terminated, no further steps are possible.";
            ]
        else text "" );
      ]
  in
  let send_interrupt =
    let warn_payload =
      model.unparsed_interrupt_payload <> ""
      && Result.is_error model.parsed_interrupt_payload
    in
    panel_block
      [
        div ~a:[ class_ "field" ]
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
                      (fun operation ->
                        Model.ChangeInterruptOperation operation)
                      Ast.string_of_operation
                      (fun operation ->
                        Some operation = model.interrupt_operation)
                      ( Ast.OperationMap.bindings
                          code.loader_state.typechecker.operations
                      |> List.map fst );
                  ];
                elt "p" ~a:[ class_ "control" ]
                  [
                    input
                      ~a:
                        [
                          class_
                            (if warn_payload then "input is-danger" else "input");
                          type_ "text";
                          oninput (fun input ->
                              Model.ParseInterruptPayload input);
                          str_prop "placeholder" "payload";
                          disabled (Option.is_none model.interrupt_operation);
                          value model.unparsed_interrupt_payload;
                        ]
                      [];
                  ];
                div ~a:[ class_ "control" ]
                  [
                    (let dis =
                       Option.is_none model.interrupt_operation
                       || Result.is_error model.parsed_interrupt_payload
                     in
                     elt "button"
                       ~a:
                         [
                           class_ "button is-info";
                           onclick (fun _ -> Model.Interrupt);
                           disabled dis;
                         ]
                       [ text "↓" ]);
                  ];
              ];
            ( match model.parsed_interrupt_payload with
            | Error msg when warn_payload ->
                elt "p" ~a:[ class_ "help is-danger" ] [ text msg ]
            | _ -> nil );
          ];
      ]
  in
  panel "Interaction"
    ~a:[ onmousemove (fun _ -> Model.SelectReduction None) ]
    ( view_undo_last_step :: view_random_steps steps
      :: List.mapi view_step steps
    @ [ send_interrupt ] )

let view_history ops =
  let view_operation op =
    ( match op with
    | Model.In (op, expr) ->
        Format.fprintf Format.str_formatter "↓ %t %t" (Ast.Operation.print op)
          (Ast.print_expression expr)
    | Model.Out (op, expr) ->
        Format.fprintf Format.str_formatter "↑ %t %t" (Ast.Operation.print op)
          (Ast.print_expression expr) );
    elt "a" ~a:[ class_ "panel-block" ] [ text (Format.flush_str_formatter ()) ]
  in
  panel "History" (List.map view_operation ops)

let view_process steps proc =
  let process_tree = RedexSelectorTM.view_process_with_redexes steps proc in
  div ~a:[ class_ "box" ] [ elt "pre" process_tree ]

let view_editor (model : Model.model) =
  div ~a:[ class_ "box" ]
    [
      elt "textarea"
        ~a:
          [
            class_ "textarea has-fixed-size";
            oninput (fun input -> Model.ChangeSource input);
            int_prop "rows"
              (max 10
                 (String.split_on_char '\n' model.unparsed_code |> List.length));
          ]
        [ text model.unparsed_code ];
    ]

(* let _view (model : Model.model) =
  match model.loaded_code with
  | Ok code ->
      div
        [
          input ~a:[type_ "range"; int_attr "min" 0; int_attr "max" 10; int_attr "step" 2; onmousedown (fun event -> Model.ParseInterrupt (string_of_int event.x))] [];
          (* elt "progress" ~a:[type_ "range"; value (string_of_int model.random_step_size); int_attr "max" 10; oninput (fun input -> Model.ChangeStepSize input)] []; *)
          editor model;
          actions model code;
          view_operations code.snapshot.operations;
          view_process code.snapshot.process;
        ]
  | Error msg -> div [ editor model; text msg ] *)

let view_compiler (model : Model.model) =
  let use_stdlib =
    elt "label" ~a:[ class_ "panel-block" ]
      [
        input
          ~a:
            [
              type_ "checkbox";
              onchange_checked (fun use_stdlib -> Model.UseStdlib use_stdlib);
              bool_prop "checked" model.use_stdlib;
            ]
          [];
        text "Load standard library";
      ]
  in
  let load_example =
    div
      ~a:[ class_ "panel-block"; style "display" "block" ]
      [
        div ~a:[ class_ "field" ]
          [
            div
              ~a:[ class_ "control is-expanded" ]
              [
                select
                  ~a:[ class_ "select is-fullwidth" ]
                  "Load example"
                  (fun (_, source) -> Model.ChangeSource source)
                  (fun (title, _) -> title)
                  (fun _ -> false)
                  Examples.examples;
              ];
          ];
      ]
  and run_process =
    panel_block
      [
        elt "button"
          ~a:
            [
              class_ "button is-info is-fullwidth";
              onclick (fun _ -> Model.LoadSource);
              (* disabled (Result.is_error model.loaded_code); *)
            ]
          [ text "Compile & run" ];
        ( match model.loaded_code with
        | Error msg -> elt "p" ~a:[ class_ "help is-danger" ] [ text msg ]
        | Ok _ -> nil );
      ]
  in
  panel "Code options" [ use_stdlib; load_example; run_process ]

let view_source model =
  div ~a:[ class_ "columns" ]
    [
      div ~a:[ class_ "column is-three-quarters" ] [ view_editor model ];
      div
        ~a:[ class_ "column is-one-quarter is-sticky" ]
        [ view_compiler model ];
    ]

let view_code (model : Model.model) (code : Model.loaded_code) =
  let steps = Model.steps code in
  let selected_red =
    match model.selected_reduction with
    | None -> None
    | Some i -> List.nth_opt steps i |> Option.map fst
  in
  div ~a:[ class_ "columns" ]
    [
      div
        ~a:[ class_ "column is-three-quarters" ]
        [ view_process selected_red code.snapshot.process ];
      div
        ~a:[ class_ "column is-one-quarter is-sticky" ]
        [ view_steps model code steps; view_history code.snapshot.operations ];
    ]

let view_navbar =
  let view_title =
    div ~a:[ class_ "navbar-brand" ]
      [
        elt "a" ~a:[ class_ "navbar-item" ]
          [ elt "p" ~a:[ class_ "title" ] [ text "Æff" ] ];
      ]
  in

  elt "navbar" ~a:[ class_ "navbar" ] [ view_title ]

let view (model : Model.model) =
  div
    [
      view_navbar;
      ( match model.loaded_code with
      | Error _ -> view_source model
      | Ok code -> view_code model code );
    ]
