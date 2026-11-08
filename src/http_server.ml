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

type request_headers = {
  content_length : int;
  filename : string option;
  duplicate_filename : bool;
}

let rec read_headers channel headers =
  match input_line channel with
  | exception End_of_file -> headers
  | line ->
      let line = trim line in
      if line = "" then headers
      else
        let headers =
          match String.index_opt line ':' with
          | None -> headers
          | Some separator ->
              let name =
                String.sub line 0 separator |> String.lowercase_ascii
              in
              let value =
                String.sub line (separator + 1)
                  (String.length line - separator - 1) |> trim
              in
              match name with
              | "content-length" ->
                  let content_length =
                    try int_of_string value with Failure _ -> 0
                  in
                  { headers with content_length }
              | "x-zfcert-filename" ->
                  { headers with
                    filename = Some value;
                    duplicate_filename = headers.filename <> None }
              | _ -> headers
        in
        read_headers channel headers

let request_filename headers =
  let invalid message =
    raise (Proof_session.Proof_error
             (1, "Invalid X-ZFCert-Filename header: " ^ message))
  in
  if headers.duplicate_filename then invalid "duplicate header";
  match headers.filename with
  | None -> None
  | Some encoded ->
      let decoded = Buffer.create (String.length encoded) in
      let hex = function
        | '0' .. '9' as character -> Char.code character - Char.code '0'
        | 'a' .. 'f' as character -> Char.code character - Char.code 'a' + 10
        | 'A' .. 'F' as character -> Char.code character - Char.code 'A' + 10
        | _ -> invalid "malformed percent escape"
      in
      let rec decode index =
        if index < String.length encoded then
          if encoded.[index] = '%' then begin
            if index + 2 >= String.length encoded then
              invalid "malformed percent escape";
            let character =
              Char.chr (hex encoded.[index + 1] * 16 + hex encoded.[index + 2])
            in
            Buffer.add_char decoded character;
            decode (index + 3)
          end else begin
            Buffer.add_char decoded encoded.[index];
            decode (index + 1)
          end
      in
      decode 0;
      let filename = Buffer.contents decoded in
      if filename = "" || Filename.is_relative filename then
        invalid "expected a nonempty absolute filename";
      if String.exists
           (fun character -> character = '\000' || character = '\r'
                             || character = '\n') filename then
        invalid "filename contains a forbidden character";
      let filename =
        try Unix.realpath filename with
        | Unix.Unix_error ((Unix.ENOENT | Unix.ENOTDIR), _, _) -> filename
        | Unix.Unix_error (error, _, _) ->
            invalid ("cannot resolve filename: " ^ Unix.error_message error)
      in
      Some filename

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
           let headers =
             read_headers input
               { content_length = 0; filename = None;
                 duplicate_filename = false }
           in
           let body =
             if headers.content_length > 0 then
               really_input_string input headers.content_length
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
                      let filename = request_filename headers in
                      let load_input =
                        Option.map (fun _ -> Native_input.load) filename
                      in
                      Proof_session.check_script ?filename ?load_input script
                      |> Api_json.success)
                   body
               in
               send_response output "200 OK"
                 "application/json; charset=utf-8" response
           | "POST", "/api/step" ->
               let response =
                 proof_response
                   (fun script ->
                      let filename = request_filename headers in
                      let load_input =
                        Option.map (fun _ -> Native_input.load) filename
                      in
                      let state, has_qed =
                        Proof_session.analyze_script ?filename ?load_input script
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
