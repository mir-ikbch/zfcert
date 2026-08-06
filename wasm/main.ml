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
  (* Keep an explicit global assignment in addition to [Js.export].  It makes
     the browser-facing name independent of whether the loader is running in
     a script or module context. *)
  Js.Unsafe.set Js.Unsafe.global (Js.string "ZfcertWasm") api;
  Js.export "ZfcertWasm" api
