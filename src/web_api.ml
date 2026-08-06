(* Pure API entry points shared by the native HTTP server and the browser
   WebAssembly bridge.  The functions return the same JSON strings as the
   HTTP endpoints, so the browser does not need to duplicate proof-session
   error handling. *)

let proof_response evaluate body =
  try evaluate body with
  | Proof_session.Proof_error (line, message) ->
      Api_json.error ~line message
  | Parser.Parse_error (_, message) ->
      Api_json.error ~line:1 message
  | exception_ ->
      Api_json.error ~line:1
        ("Internal error: " ^ Printexc.to_string exception_)

let check script =
  proof_response
    (fun script ->
       Proof_session.check_script script |> Api_json.success)
    script

let step script =
  proof_response
    (fun script ->
       let state, has_qed = Proof_session.analyze_script script in
       Api_json.step state ~has_qed)
    script

let axioms () = Api_json.axioms ()
