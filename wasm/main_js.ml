open Js_of_ocaml

let api =
  object%js
    method check script =
      Js.string (Web_api.check (Js.to_string script))

    method step script =
      Js.string (Web_api.step (Js.to_string script))

    val axioms = Js.string (Web_api.axioms ())
  end

let () =
  Js.Unsafe.set Js.Unsafe.global (Js.string "ZfcertJs") api;
  Js.export "ZfcertJs" api
