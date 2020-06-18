open Js_browser

let app =
  Vdom.simple_app ~init:Model.init ~view:View.view ~update:Model.update ()

let run () =
  Vdom_blit.run app |> Vdom_blit.dom
  |> Element.append_child
       ( match Document.get_element_by_id document "container" with
       | Some element -> element
       | None -> Document.document_element document )

let () = Window.set_onload window run
