let trim = String.trim

let starts_with text prefix =
  let prefix_length = String.length prefix in
  prefix_length <= String.length text
  && String.sub text 0 prefix_length = prefix

let read_file path =
  let channel = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr channel)
    (fun () ->
       really_input_string channel (in_channel_length channel))

let mime_type path =
  if Filename.check_suffix path ".html" then "text/html; charset=utf-8"
  else if Filename.check_suffix path ".css" then "text/css; charset=utf-8"
  else if Filename.check_suffix path ".js" then
    "application/javascript; charset=utf-8"
  else if Filename.check_suffix path ".wasm" then "application/wasm"
  else "application/octet-stream"

let send_response channel status content_type body =
  Printf.fprintf channel "HTTP/1.1 %s\r\n" status;
  Printf.fprintf channel "Content-Type: %s\r\n" content_type;
  Printf.fprintf channel "Content-Length: %d\r\n" (String.length body);
  Printf.fprintf channel "Cache-Control: no-store\r\n";
  Printf.fprintf channel "Connection: close\r\n\r\n";
  output_string channel body;
  flush channel

let rec read_headers channel content_length =
  match input_line channel with
  | exception End_of_file -> content_length
  | line ->
      let line = trim line in
      if line = "" then content_length
      else
        let prefix = "content-length:" in
        let content_length =
          if starts_with (String.lowercase_ascii line) prefix then
            let value =
              String.sub line (String.length prefix)
                (String.length line - String.length prefix)
            in
            try int_of_string (trim value) with Failure _ -> 0
          else content_length
        in
        read_headers channel content_length

let proof_response evaluate body =
  try evaluate body with
  | Proof_session.Proof_error (line, message) ->
      Api_json.error ~line message
  | Parser.Parse_error (_, message) ->
      Api_json.error ~line:1 message
  | exception_ ->
      Api_json.error ~line:1
        ("Internal error: " ^ Printexc.to_string exception_)

let serve_static channel web_root resource =
  let relative =
    if resource = "/" || resource = "/index.html" then "index.html"
    else String.sub resource 1 (String.length resource - 1)
  in
  let path = Filename.concat web_root relative in
  try
    send_response channel "200 OK" (mime_type path) (read_file path)
  with Sys_error _ ->
    send_response channel "404 Not Found" "text/plain; charset=utf-8"
      ("Resource not found: " ^ relative)

let safe_static_path path =
  let segments = String.split_on_char '/' path in
  not (List.exists (fun segment -> segment = "..") segments)

let handle_client web_root socket =
  let input = Unix.in_channel_of_descr socket in
  let output = Unix.out_channel_of_descr socket in
  Fun.protect
    ~finally:(fun () -> close_in_noerr input; close_out_noerr output)
    (fun () ->
       match input_line input with
       | exception End_of_file -> ()
       | request ->
           let method_, path =
             match String.split_on_char ' ' (trim request) with
             | method_ :: path :: _ -> (method_, path)
             | _ -> ("", "")
           in
           let content_length = read_headers input 0 in
           let body =
             if content_length > 0 then
               really_input_string input content_length
             else ""
           in
           match method_, path with
           | "GET", "/api/health" ->
               send_response output "200 OK"
                 "application/json; charset=utf-8"
                 {|{"ok":true,"service":"zfcert","kernel":"coq-extracted"}|}
           | "GET", "/api/axioms" ->
               send_response output "200 OK"
                 "application/json; charset=utf-8"
                 (Api_json.axioms ())
           | "POST", "/api/check" ->
               let response =
                 proof_response
                   (fun script ->
                      Proof_session.check_script script |> Api_json.success)
                   body
               in
               send_response output "200 OK"
                 "application/json; charset=utf-8" response
           | "POST", "/api/step" ->
               let response =
                 proof_response
                   (fun script ->
                      let state, has_qed =
                        Proof_session.analyze_script script
                      in
                      Api_json.step state ~has_qed)
                   body
               in
               send_response output "200 OK"
                 "application/json; charset=utf-8" response
           | "GET", path
             when safe_static_path path
                  && (path = "/" || path = "/index.html"
                      || path = "/style.css" || path = "/app.js"
                      || starts_with path "/wasm/") ->
               serve_static output web_root path
           | _ ->
               send_response output "404 Not Found"
                 "application/json; charset=utf-8"
                 {|{"error":"not found"}|})

let serve ~web_root ~port =
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  let socket = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  Unix.setsockopt socket Unix.SO_REUSEADDR true;
  Unix.bind socket (Unix.ADDR_INET (Unix.inet_addr_loopback, port));
  Unix.listen socket 32;
  Printf.printf "ZFCert: http://127.0.0.1:%d\n%!" port;
  while true do
    let client, _ = Unix.accept socket in
    try handle_client web_root client with
    | exception_ ->
        prerr_endline
          ("Request failed: " ^ Printexc.to_string exception_);
        Unix.close client
  done
