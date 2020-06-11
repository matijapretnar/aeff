open Vdom

let button txt msg = input [] ~a:[onclick (fun _ -> msg); type_button; value txt]
let disabled_button txt = input [] ~a:[type_button; value txt; disabled true]

let pre txt =
    elt "pre" ~a:[style "background" "#ddd"; style "font-family" "\"Lucida Console\", Monaco, monospace"; style "font-size" "smaller"] [text txt]

let h1 txt = elt "h1" [text txt]

let step_description path = String.concat ">" path

let step_action (path, step) =
    elt "li" [
        button (step_description path) (Model.Step step)
    ]

let actions (model : Model.model) =
    let step_actions = List.map step_action model.state.steps in
    let random_action =
        let random_step_button = 
            match model.random_step_size with
            | Error msg -> disabled_button msg
            | Ok num_steps -> button (Format.sprintf "make %d random steps" num_steps) Model.RandomStep
        in
        elt "li" [div [
            input ~a:[oninput (fun input -> Model.ChangeStepSize input); value model.unparsed_step_size] [];
            random_step_button
        ]]
    and back_action =
        match model.history with
        | [] -> disabled_button "back" :: []
        | _ -> button "back" Model.Back :: []
    and interrupt_action =
        let interrupt_button = 
            match model.parsed_interrupt with
            | Error msg -> disabled_button msg
            | Ok _ -> button "interrupt" Model.Interrupt
        in
        elt "li" [div [
            input ~a:[oninput (fun input -> Model.ParseInterrupt input)] [];
            interrupt_button
        ]]
    in
    elt "ol" (back_action @ [random_action] @ step_actions @ [interrupt_action])

let operations ops =
    let operation op =
        begin match op with
        | Model.In (op, expr) -> Format.fprintf Format.str_formatter "↓%t %t" (Ast.Operation.print op) (Ast.print_expression expr)
        | Model.Out (op, expr) -> Format.fprintf Format.str_formatter "↑%t %t" (Ast.Operation.print op) (Ast.print_expression expr)
        end;
        elt "li" [text (Format.flush_str_formatter ())]
    in
    elt "ul" (List.map operation ops)

let process proc =
    let txt = Ast.string_of_process proc in
    pre txt

let view (model : Model.model) = 
    div [actions model; operations model.state.operations; process model.state.process]
