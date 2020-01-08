module Html = Cow.Html

let computation comp =
    Ast.print_computation comp Format.str_formatter ;
    let str = Format.flush_str_formatter () in
    Html.(pre (string str))

let form url nodes =
  Html.(
    tag "form" ~attrs:[("action", url); ("method", "GET")] (list nodes)
  )

let button node =
  Html.tag "button" node

let text_input name =
  Html.input ~attrs:[("name", name)] ""

let checkbox name =
  Html.input ~attrs:[("type", "checkbox"); ("name", name)] ""

let actions comps =
  let step index =
      Html.(form (Format.sprintf "http://127.0.0.1:8080/step/%d/" index) [
        button (string (Format.sprintf "STEP %d" (index + 1)))
      ])
  and operation =
      Html.(form "http://127.0.0.1:8080/operation/" [
        text_input "operation";
        list (List.mapi (fun i _ -> checkbox (string_of_int i)) comps);
        button (string "TRIGGER")
      ])
  in
    operation :: List.mapi (fun i _ -> step i) comps

let content comps = Html.([
    h1 (string "Computations");
    list (actions comps);
    ol (List.map computation comps)
])

let show comps =
  Html.to_string (Html.(
    html (list [
      head (list [
        base (Uri.of_string "http://www.example.com");
        meta ~charset:"UTF-8" [];
        title (string "An application with a long head");
        link ~rel:"stylesheet" (Uri.of_string "default.css");
        link ~rel:"stylesheet alternate"
             ~title:"Big text"
             (Uri.of_string "big.css");
        script ~src:(Uri.of_string "support.js") empty;
        meta ~name:"application-name"
             ~content:"Long headed application"
             []
      ]);

      body (list (content comps))
    ])
  ))
