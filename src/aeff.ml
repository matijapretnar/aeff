open Js_browser

let app =
  Vdom.simple_app ~init:Model.init ~view:View.view ~update:Model.update ()

let run () =
  Vdom_blit.run app |> Vdom_blit.dom
  |> Element.append_child (Document.body document)

let () = Window.set_onload window run
