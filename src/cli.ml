let run () =
  let port = ref 8080 in
  let web_root = ref "web" in
  let self_test = ref false in
  let options =
    [
      ("--port", Arg.Set_int port, "listen port (default: 8080)");
      ("--web-root", Arg.Set_string web_root, "directory containing web assets");
      ("--self-test", Arg.Set self_test, "run kernel tests and exit");
    ]
  in
  Arg.parse options (fun _ -> ()) "zfcert [--port PORT]";
  if !self_test then Self_test.run ()
  else Http_server.serve ~web_root:!web_root ~port:!port
