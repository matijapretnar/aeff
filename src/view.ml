module Html = Cow.Html

type message =
  | Info of string
  | Warning of string

let computation comp =
    Ast.print_computation comp Format.str_formatter ;
    let str = Format.flush_str_formatter () in
    Html.(li (pre ~attrs:[("style", "background: #ddd; font-family: \"Lucida Console\", Monaco, monospace; font-size: smaller")] (string str)))

let form url nodes =
  Html.(
    tag "form" ~attrs:[("action", url); ("method", "GET"); ("style", "display: inline")] (list nodes)
  )

let button node =
  Html.tag "button" node

let text_input name =
  Html.input ~attrs:[("name", name)] ""

let checkbox name =
  Html.input ~attrs:[("type", "checkbox"); ("name", name)] ""

let message msg =
  Html.(
    match msg with
    | Info msg -> li (string msg)
    | Warning msg -> li (span ~attrs:[("style", "color: red")] (string msg))
  )

let actions comps =
  let step index =
      Html.(form (Format.sprintf "http://127.0.0.1:8080/step/%d/" index) [
        button (string (Format.sprintf "STEP COMP. %d" (index + 1)))
      ])
  and random_step =
      Html.(form (Format.sprintf "http://127.0.0.1:8080/step/random/1/") [
        button (string (Format.sprintf "STEP RANDOM"))
      ])
  and only_step =
      Html.(form (Format.sprintf "http://127.0.0.1:8080/step/random/1/") [
        button (string (Format.sprintf "STEP COMP."))
      ])
  and step10 =
      Html.(form (Format.sprintf "http://127.0.0.1:8080/step/random/10/") [
        button (string (Format.sprintf "STEP RANDOM 10X"))
      ])
  and back =
      Html.(form (Format.sprintf "http://127.0.0.1:8080/back/") [
        button (string (Format.sprintf "STEP BACK"))
      ])
  and operation =
      Html.(form "http://127.0.0.1:8080/operation/" [
        text_input "operation";
        button (string "TRIGGER INTERRUPT")
      ])
  in
    match comps with
    | [_] -> back :: only_step :: step10 :: operation :: []
    | _ -> back :: List.mapi (fun i _ -> step i) comps @ random_step :: step10 :: operation :: []

let content comps msgs = Html.([
    h1 (string "An interactive interpreter for Æff");
    list (actions comps);
    ol (List.map computation comps)
    (* ol (List.map message msgs) *)
])

let help =
  Html.(ul [ string "STEP BACK - take one step back in the evaluation" ;
             string "STEP COMP. X - advance computation X by one step" ;
             string "STEP RANDOM - advance a random computation by one step" ;
             string "STEP RANDOM 10X - advance the computations randomly by 10 steps" ;
             string "TRIGGER INTERRUPT - trigger the interrupt and its payload that you have entered in the input box"])

let show (comps, msgs) =
  Html.to_string (Html.(
    html ~attrs:[("style", "font-family: Arial, Helvetica, sans-serif")] (list [
      head (list [
        base (Uri.of_string "http://127.0.0.1:8080/");
        meta ~charset:"UTF-8" [];
        title (string "An interactive interpreter for Æff");
        link ~rel:"stylesheet" (Uri.of_string "default.css");
        link ~rel:"stylesheet alternate"
             ~title:"Big text"
             (Uri.of_string "big.css");
        script ~src:(Uri.of_string "support.js") empty;
        meta ~name:"application-name"
             ~content:"An interactive interpreter for Æff"
             []
      ]);

      body (list (content comps msgs));
      body (br);
      body (b (string "HELP:"));
      body help
    ])
  ))
