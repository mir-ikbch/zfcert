let read_file path =
  let channel = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr channel)
    (fun () -> really_input_string channel (in_channel_length channel))

let check_file path =
  try
    let script = read_file path in
    let state = Proof_session.check_script script in
    let theorem = Proof_session.theorem_name state in
    if theorem = "" then
      Printf.printf "OK: %s (declarations checked)\n%!" path
    else
      Printf.printf "OK: %s (theorem %s verified)\n%!" path theorem
  with
  | Proof_session.Proof_error (line, message) ->
      Printf.eprintf "Error: %s:%d: %s\n%!" path line message;
      exit 1
  | Parser.Parse_error (_, message) ->
      Printf.eprintf "Error: %s: %s\n%!" path message;
      exit 1
  | Sys_error message ->
      Printf.eprintf "Error: cannot read %s: %s\n%!" path message;
      exit 1

let run () =
  let port = ref 8080 in
  let web_root = ref "web" in
  let self_test = ref false in
  let check_path = ref None in
  let options =
    [
      ("--port", Arg.Set_int port, "listen port (default: 8080)");
      ("--web-root", Arg.Set_string web_root, "directory containing web assets");
      ("--self-test", Arg.Set self_test, "run kernel tests and exit");
      ("--check", Arg.String (fun path -> check_path := Some path),
       "check one .zfp file and exit");
    ]
  in
  Arg.parse options
    (fun argument ->
       raise (Arg.Bad ("unexpected argument: " ^ argument)))
    "zfcert [--check FILE] [--port PORT]";
  match !self_test, !check_path with
  | true, Some _ ->
      prerr_endline "Error: --self-test and --check cannot be used together.";
      exit 2
  | true, None -> Self_test.run ()
  | false, Some path -> check_file path
  | false, None -> Http_server.serve ~web_root:!web_root ~port:!port
