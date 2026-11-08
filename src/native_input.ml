let read_file path =
  let channel = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr channel)
    (fun () -> really_input_string channel (in_channel_length channel))

let load ~from filename =
  if String.contains filename '\000' then
    raise (Sys_error "The input filename must not contain a null character.");
  let path =
    if Filename.is_relative filename then
      let directory =
        match from with
        | Some source -> Filename.dirname source
        | None -> Sys.getcwd ()
      in
      Filename.concat directory filename
    else filename
  in
  try
    let canonical_path = Unix.realpath path in
    (canonical_path, read_file canonical_path)
  with Unix.Unix_error (error, _, _) ->
    raise (Sys_error (path ^ ": " ^ Unix.error_message error))
