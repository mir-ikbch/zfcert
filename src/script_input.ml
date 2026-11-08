type loader = from:string option -> string -> string * string

type origin = {
  filename : string option;
  line : int;
  root_input_line : int option;
}

type t = {
  expanded_statements : (int * string) list;
  origins : (int, origin) Hashtbl.t;
  final_line : int;
}

exception Error of int * string

let source_error origin message =
  match origin.root_input_line, origin.filename with
  | Some root_line, Some filename ->
      (root_line, Printf.sprintf "%s:%d: %s" filename origin.line message)
  | Some root_line, None -> (root_line, message)
  | None, _ -> (origin.line, message)

let raise_error origin message =
  let line, message = source_error origin message in
  raise (Error (line, message))

let is_space = function
  | ' ' | '\t' | '\r' | '\n' -> true
  | _ -> false

let input_argument statement =
  let length = String.length statement in
  let rec word_end index =
    if index = length || is_space statement.[index] then index
    else word_end (index + 1)
  in
  let index = word_end 0 in
  if String.lowercase_ascii (String.sub statement 0 index) <> "input" then
    None
  else
    Some (String.trim (String.sub statement index (length - index)))

let parse_filename origin argument =
  let invalid () =
    raise_error origin "Expected input \"filename\". with a double-quoted filename."
  in
  let length = String.length argument in
  if length = 0 || argument.[0] <> '"' then invalid ();
  let buffer = Buffer.create length in
  let rec read index =
    if index >= length then invalid ();
    match argument.[index] with
    | '"' ->
        if String.trim (String.sub argument (index + 1) (length - index - 1)) <> ""
        then raise_error origin "Unexpected text after the input filename.";
        let filename = Buffer.contents buffer in
        if filename = "" then raise_error origin "The input filename must not be empty.";
        filename
    | '\n' | '\r' ->
        raise_error origin "The input filename must not contain a newline."
    | '\\' when index + 1 < length
                && (argument.[index + 1] = '\\' || argument.[index + 1] = '"') ->
        Buffer.add_char buffer argument.[index + 1];
        read (index + 2)
    | character ->
        Buffer.add_char buffer character;
        read (index + 1)
  in
  read 1

let last_line source =
  1 + String.fold_left (fun count c -> if c = '\n' then count + 1 else count) 0 source

let expand ?filename ?load_input source =
  let origins = Hashtbl.create 64 in
  let next_id = ref 0 in
  let register origin =
    incr next_id;
    Hashtbl.add origins !next_id origin;
    !next_id
  in
  let final_origin =
    ref { filename; line = last_line source; root_input_line = None }
  in
  let rec expand_source filename root_input_line active_files depth source accumulated =
    let source_origin line = { filename; line; root_input_line } in
    let source_end = source_origin (last_line source) in
    let source_statements =
      try Parser.split_statements source with
      | Parser.Statement_error (line, message) ->
          raise_error (source_origin line) message
    in
    List.fold_left
      (fun accumulated (line, statement) ->
        let origin = source_origin line in
        match input_argument statement with
        | None ->
            final_origin := source_end;
            (register origin, statement) :: accumulated
        | Some argument ->
            let requested = parse_filename origin argument in
            let load =
              match load_input with
              | Some load -> load
              | None ->
                  raise_error origin "input requires native file access; no input loader is available."
            in
            if depth >= 128 then
              raise_error origin "Maximum input nesting depth (128) exceeded.";
            let included_filename, contents =
              try load ~from:filename requested with
              | Sys_error message | Failure message ->
                  raise_error origin
                    (Printf.sprintf "Cannot input %S: %s" requested message)
            in
            if List.mem included_filename active_files then
              raise_error origin
                (Printf.sprintf "Circular input detected for %S." included_filename);
            let root_line = Option.value root_input_line ~default:line in
            expand_source (Some included_filename) (Some root_line)
              (included_filename :: active_files) (depth + 1) contents accumulated)
      accumulated source_statements
  in
  let active_files = match filename with None -> [] | Some filename -> [filename] in
  let expanded_statements =
    expand_source filename None active_files 0 source [] |> List.rev
  in
  let final_line = register !final_origin in
  { expanded_statements; origins; final_line }

let statements expanded = expanded.expanded_statements

let error expanded line message =
  match Hashtbl.find_opt expanded.origins line with
  | Some origin -> source_error origin message
  | None -> (line, message)

let end_line expanded = expanded.final_line
