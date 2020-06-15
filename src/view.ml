open Vdom

let panel heading blocks =
  div ~a:[ class_ "panel" ]
    (elt "p" ~a:[ class_ "panel-heading" ] [ text heading ] :: blocks)

let panel_block = div ~a:[ class_ "panel-block" ]

let examples =
  [
    ( "feed",
      "\n\
      \  let absurd void = (match void with)\n\n\
       (* Booleans *)\n\
       let not x = if x then false else true\n\n\
       type 'a option = None | Some of 'a\n\
       let rec assoc x = function\n\
      \  | [] |-> None\n\
      \  | (key, v) :: lst |-> if x = key then Some v else assoc x lst\n\n\
       let rec range m n =\n\
      \  if m > n then\n\
      \    []\n\
      \  else\n\
      \    m :: range (m + 1) n\n\n\
       let reverse lst =\n\
      \  let rec reverse_acc acc = function\n\
      \    | [] |-> acc\n\
      \    | x :: xs |-> reverse_acc (x :: acc) xs\n\
      \  in\n\
      \  reverse_acc [] lst\n\n\
       let rec map f = function\n\
      \  | [] |-> []\n\
      \  | x :: xs |->\n\
      \    let y = f x in\n\
      \    let ys = map f xs in\n\
      \    y :: ys\n\n\
       let hd = function\n\
      \  | x :: _ |-> x\n\n\
       let tl = function\n\
      \  | x :: xs |-> xs\n\n\
       let take f k =\n\
      \  let r = range 0 k in map f r\n\n\
       let rec fold_left f acc = function\n\
      \  | [] |-> acc\n\
      \  | y :: ys |->\n\
      \    let acc' = f acc y in\n\
      \    fold_left f acc' ys\n\n\
       let rec fold_right f xs acc =\n\
      \  match xs with\n\
      \    | [] |-> acc\n\
      \    | x :: xs |->\n\
      \      let acc' = fold_right f xs acc in\n\
      \      f x acc'\n\
      \    \n\
      \    let rec iter f = function\n\
      \  | [] |-> ()\n\
      \  | x :: xs |-> f x; iter f xs\n\n\
       let rec forall p = function\n\
      \  | [] |-> true\n\
      \  | x :: xs |-> if p x then forall p xs else false\n\n\
       let rec exists p = function\n\
      \  | [] |-> false\n\
      \  | x :: xs |-> if p x then true else exists p xs\n\n\
       let mem x = exists (fun x' |-> x = x')\n\
       let rec filter p = function\n\
      \  | [] |-> []\n\
      \  | x :: xs |->\n\
      \    if p x then (x :: filter p xs) else filter p xs\n\n\
       let complement xs ys = filter (fun x |-> not (mem x ys)) xs\n\
       let intersection xs ys = filter (fun x |-> mem x ys) xs\n\
       let rec zip xs ys =\n\
      \  match (xs, ys) with\n\
      \  | ([], []) |-> []\n\
      \  | (x :: xs, y :: ys) |-> (x, y) :: (zip xs ys)\n\n\
       let rec unzip = function\n\
      \  | [] |-> ([], [])\n\
      \  | (x, y) :: xys |->\n\
      \    let xs, ys = unzip xys in\n\
      \    (x :: xs, y :: ys)\n\n\
       let rec (@) (xs, ys) =\n\
      \  match xs with\n\
      \  | [] |-> ys\n\
      \  | x :: xs |-> x :: (xs @ ys)\n\n\
       let rec length = function\n\
      \  | [] |-> 0\n\
      \  | x :: xs |-> length xs + 1\n\n\
       let rec nth (x::xs) n =\n\
      \  if n = 0 then x else nth xs (n - 1)\n\n\
       (* Basic functions *)\n\
       let abs x = if x < 0 then -x else x\n\
       let min x y = if x < y then x else y\n\
       let max x y = if x < y then y else x\n\
       let rec gcd m n =\n\
      \  match n with\n\
      \  | 0 |-> m\n\
      \  | _ |-> let g = gcd n in g (m mod n)\n\n\
       let rec lcm m n =\n\
      \  let d = gcd m n in (m * n) / d\n\n\
       let odd x = (x mod 2) = 1\n\
       let even x = (x mod 2) = 0\n\
       let id x = x\n\
       let compose f g x = f (g x)\n\
       let (|>) x f = f x\n\
       let ignore _ = ()\n\
       let fst (x, _) = x\n\
       let snd (_, y) = y\n\
      \  \n\
       let return x = x\n\n\
       let awaitValue p =\n\
      \    await p until <<value>> in return value\n\n\
       operation request : int\n\
       operation response : int list\n\
       operation nextItem : unit\n\
       operation display : string\n\
       operation batchSizeRequest : unit\n\
       operation batchSizeResponse : int\n\n\n\
       let client () =\n\
      \    let cachedData = ref [] in\n\
      \    let requestInProgress = ref false in\n\
      \    let currentItem = ref 0 in\n\n\
      \    send batchSizeRequest ();\n\
      \    promise (batchSizeResponse batchSize |-> return <<batchSize>>) as \
       batchSizePromise in\n\n\
      \    let requestNewData offset =\n\
      \        requestInProgress := true;\n\
      \        send request offset;\n\
      \        promise (response newBatch |->\n\
      \            cachedData := !cachedData @ newBatch;\n\
      \            requestInProgress := false;\n\
      \            return <<()>>)\n\
      \        as _ in\n\
      \        return ()\n\
      \    in\n\n\
      \    let rec clientLoop batchSize =\n\
      \        promise (nextItem () |->\n\
      \            let cachedSize = length !cachedData in\n\
      \            (if (!currentItem > cachedSize - batchSize / 2) && (not \
       !requestInProgress) then\n\
      \                 requestNewData (cachedSize + 1)\n\
      \             else\n\
      \                 return ());\n\
      \            (if (!currentItem) < cachedSize then\n\
      \                 send display (toString (nth !cachedData !currentItem));\n\
      \                 currentItem := !currentItem + 1\n\
      \             else  \n\
      \                 send display \"please wait a bit and try again\");\n\
      \            clientLoop batchSize)\n\
      \        as p in\n\
      \        return p\n\
      \    in\n\n\
      \    await batchSizePromise until <<batchSize>> in\n\
      \    clientLoop batchSize\n\n\
       let server batchSize =\n\
      \    let rec waitForBatchSize () =\n\
      \        promise (batchSizeRequest () |->\n\
      \            send batchSizeResponse batchSize;\n\
      \            waitForBatchSize ())\n\
      \        as p in\n\
      \        return p\n\
      \    in\n\
      \    let rec waitForRequest () =\n\
      \        promise (request offset |->\n\
      \            let payload = map (fun x |-> 10 * x) (range offset (offset \
       + batchSize - 1)) in\n\
      \            send response payload;\n\
      \            waitForRequest ())\n\
      \        as p in\n\
      \        return p\n\
      \    in\n\
      \    waitForBatchSize ();\n\
      \    waitForRequest ()\n\n\n\
       let rec user () =\n\
      \    let rec wait n = \n\
      \      if n = 0 then return () else wait (n - 1)\n\
      \    in\n\
      \    send nextItem ();\n\
      \    wait 10;\n\
      \    user ()\n\n\n\
       run (server 42)\n\
       run (client ())\n\
       run (user ())\n" );
  ]

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
  and view_random_steps step_sizes =
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
                    ]
                  [ text "random steps" ];
              ];
          ];
      ]
  in
  panel "Step process"
    ( view_undo_last_step
    :: view_random_steps [ 1; 2; 4; 8; 16; 32; 64; 128; 256; 512; 1024 ]
    :: List.map view_step (Model.steps code) )

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
            class_ "textarea";
            oninput (fun input -> Model.ChangeSource input);
            int_prop "rows" 20;
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
  panel "Code options"
    [
      panel_block
        [
          elt "button"
            ~a:
              [
                class_ "button is-primary is-fullwidth";
                onclick (fun _ -> Model.LoadSource);
                disabled (Result.is_error model.loaded_code);
              ]
            [ text "Run process" ];
          ( match model.loaded_code with
          | Error msg -> elt "p" ~a:[ class_ "help is-danger" ] [ text msg ]
          | Ok _ -> nil );
        ];
    ]

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
  and view_examples =
    let view_example (title, source) =
      elt "a"
        ~a:
          [ class_ "navbar-item"; onclick (fun _ -> Model.ChangeSource source) ]
        [ text title ]
    in
    div ~a:[ class_ "navbar-menu" ]
      [
        div ~a:[ class_ "navbar-start" ]
          [
            div
              ~a:[ class_ "navbar-item has-dropdown is-hoverable" ]
              [
                elt "a" ~a:[ class_ "navbar-link" ] [ text "Load example" ];
                div
                  ~a:[ class_ "navbar-dropdown" ]
                  (List.map view_example examples);
              ];
          ];
      ]
  in

  elt "navbar" ~a:[ class_ "navbar" ] [ view_title; view_examples ]

let view (model : Model.model) =
  div
    [
      view_navbar;
      ( match model.loaded_code with
      | Error _ | Ok None -> view_source model
      | Ok (Some code) -> view_code model code );
    ]
