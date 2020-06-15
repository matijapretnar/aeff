open Vdom

let panel heading blocks =
  div ~a:[ class_ "panel" ]
    (elt "p" ~a:[ class_ "panel-heading" ] [ text heading ] :: blocks)

let panel_block = div ~a:[ class_ "panel-block" ]

let button txt msg =
  input [] ~a:[ onclick (fun _ -> msg); type_button; value txt ]

let disabled_button txt = input [] ~a:[ type_button; value txt; disabled true ]

let nil = text ""

let step_description path = String.concat ">" path

let step_action (path, step) =
  elt "li" [ button (step_description path) (Model.Step step) ]

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

let view_steps (model : Model.model) (code : Model.loaded_code) =
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
  and view_step (path, step) =
    panel_block
      [
        elt "button"
          ~a:
            [
              class_ "button is-outlined is-fullwidth";
              onclick (fun _ -> Model.Step step);
            ]
          [ text (step_description path) ];
      ]
  and view_random_steps step_sizes steps =
    let step_option step_size =
      elt "option"
        ~a:[ bool_prop "selected" (step_size = model.random_step_size) ]
        [ text (string_of_int step_size) ]
    in
    div
      ~a:[ class_ "panel-block"; style "display" "block" ]
      [
        div
          ~a:[ class_ "field has-addons" ]
          [
            div
              ~a:[ class_ "control is-expanded" ]
              [
                div
                  ~a:[ class_ "select is-fullwidth is-success" ]
                  [
                    elt "select"
                      ~a:
                        [
                          onchange_index (fun i ->
                              Model.ChangeRandomStepSize (List.nth step_sizes i));
                          disabled (steps = []);
                        ]
                      (List.map step_option step_sizes);
                  ];
              ];
            div ~a:[ class_ "control" ]
              [
                elt "button"
                  ~a:
                    [
                      class_ "button is-success";
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
  let steps = Model.steps code in
  panel "Step process"
    ( view_undo_last_step
    :: view_random_steps [ 1; 2; 4; 8; 16; 32; 64; 128; 256; 512; 1024 ] steps
    :: List.map view_step steps )

let view_operations (model : Model.model) ops =
  let send_interrupt =
    panel_block
      [
        div ~a:[ class_ "field" ]
          [
            div
              ~a:[ class_ "field has-addons" ]
              [
                elt "p" ~a:[ class_ "control" ]
                  [ elt "a" ~a:[ class_ "button is-static" ] [ text "↓" ] ];
                elt "p" ~a:[ class_ "control" ]
                  [
                    input
                      ~a:
                        [
                          class_ "input";
                          type_ "text";
                          oninput (fun input -> Model.ParseInterrupt input);
                          str_prop "placeholder" "opName payload";
                        ]
                      [];
                  ];
                div ~a:[ class_ "control" ]
                  [
                    elt "a"
                      ~a:
                        [
                          class_ "button";
                          onclick (fun _ -> Model.Interrupt);
                          disabled (Result.is_error model.parsed_interrupt);
                        ]
                      [ text "Send" ];
                  ];
              ];
            ( match model.parsed_interrupt with
            | Error msg -> elt "p" ~a:[ class_ "help is-danger" ] [ text msg ]
            | Ok _ -> nil );
          ];
      ]
  and view_operation op =
    ( match op with
    | Model.In (op, expr) ->
        Format.fprintf Format.str_formatter "↓ %t %t" (Ast.Operation.print op)
          (Ast.print_expression expr)
    | Model.Out (op, expr) ->
        Format.fprintf Format.str_formatter "↑ %t %t" (Ast.Operation.print op)
          (Ast.print_expression expr) );
    elt "a" ~a:[ class_ "panel-block" ] [ text (Format.flush_str_formatter ()) ]
  in
  panel "Operations" (send_interrupt :: List.map view_operation ops)

let view_process proc =
  let txt = Ast.string_of_process proc in
  div ~a:[ class_ "box" ] [ elt "pre" [ text txt ] ]

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
  let use_pervasives =
    elt "label" ~a:[ class_ "panel-block" ]
      [
        input
          ~a:
            [
              type_ "checkbox";
              onchange_checked (fun use_pervasives ->
                  Model.UsePervasives use_pervasives);
              bool_prop "checked" model.use_pervasives;
            ]
          [];
        text "Use pervasives";
      ]
  in
  let example_option (title, _) = elt "option" [ text title ] in
  let load_example =
    div
      ~a:[ class_ "panel-block"; style "display" "block" ]
      [
        div ~a:[ class_ "field" ]
          [
            div
              ~a:[ class_ "control is-expanded" ]
              [
                div
                  ~a:[ class_ "select is-fullwidth is-success" ]
                  [
                    elt "select"
                      ~a:
                        [
                          onchange_index (fun i ->
                              Model.ChangeSource
                                (snd (List.nth Examples.examples (i - 1))));
                        ]
                      ( elt "option"
                          ~a:[ disabled true; bool_prop "selected" true ]
                          [ text "Load example" ]
                      :: List.map example_option Examples.examples );
                  ];
              ];
          ];
      ]
  and run_process =
    panel_block
      [
        elt "button"
          ~a:
            [
              class_ "button is-primary is-fullwidth";
              onclick (fun _ -> Model.LoadSource);
              (* disabled (Result.is_error model.loaded_code); *)
            ]
          [ text "Run process" ];
        ( match model.loaded_code with
        | Error msg -> elt "p" ~a:[ class_ "help is-danger" ] [ text msg ]
        | Ok _ -> nil );
      ]
  in
  panel "Code options" [ use_pervasives; load_example; run_process ]

let view_source model =
  div ~a:[ class_ "columns" ]
    [
      div ~a:[ class_ "column is-four-fifths" ] [ view_editor model ];
      div ~a:[ class_ "column is-one-fifth" ] [ view_compiler model ];
    ]

let view_code model (code : Model.loaded_code) =
  div ~a:[ class_ "columns" ]
    [
      div
        ~a:[ class_ "column is-four-fifths" ]
        [ view_process code.snapshot.process ];
      div
        ~a:[ class_ "column is-one-fifth" ]
        [
          view_steps model code; view_operations model code.snapshot.operations;
        ];
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
