open Syntax

type token =
  | Ident of string
  | Lparen | Rparen | Comma
  | Equal | NotEqual | Member
  | TNot | TAnd | TOr | TImp | TIff
  | TForall | TExists | TBottom
  | Eof

exception Parse_error of int * string
exception Statement_error of int * string

let starts_with_at input index prefix =
  let length = String.length prefix in
  index + length <= String.length input
  && String.sub input index length = prefix

let is_ascii_ident_char = function
  | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' -> true
  | _ -> false

let lex input =
  let length = String.length input in
  let rec loop index tokens =
    if index >= length then List.rev (Eof :: tokens)
    else
      match input.[index] with
      | ' ' | '\t' | '\r' | '\n' -> loop (index + 1) tokens
      | '(' -> loop (index + 1) (Lparen :: tokens)
      | ')' -> loop (index + 1) (Rparen :: tokens)
      | ',' -> loop (index + 1) (Comma :: tokens)
      | '=' -> loop (index + 1) (Equal :: tokens)
      | '~' -> loop (index + 1) (TNot :: tokens)
      | '&' -> loop (index + 1) (TAnd :: tokens)
      | '|' -> loop (index + 1) (TOr :: tokens)
      | _ when starts_with_at input index "<->" ->
          loop (index + 3) (TIff :: tokens)
      | _ when starts_with_at input index "->" ->
          loop (index + 2) (TImp :: tokens)
      | _ when starts_with_at input index "!=" ->
          loop (index + 2) (NotEqual :: tokens)
      | _ when starts_with_at input index "⊥" ->
          loop (index + String.length "⊥") (TBottom :: tokens)
      | _ when starts_with_at input index "¬" ->
          loop (index + String.length "¬") (TNot :: tokens)
      | _ when starts_with_at input index "∧" ->
          loop (index + String.length "∧") (TAnd :: tokens)
      | _ when starts_with_at input index "∨" ->
          loop (index + String.length "∨") (TOr :: tokens)
      | _ when starts_with_at input index "→" ->
          loop (index + String.length "→") (TImp :: tokens)
      | _ when starts_with_at input index "↔" ->
          loop (index + String.length "↔") (TIff :: tokens)
      | _ when starts_with_at input index "∈" ->
          loop (index + String.length "∈") (Member :: tokens)
      | _ when starts_with_at input index "∀" ->
          loop (index + String.length "∀") (TForall :: tokens)
      | _ when starts_with_at input index "∃" ->
          loop (index + String.length "∃") (TExists :: tokens)
      | character when is_ascii_ident_char character ->
          let next = ref (index + 1) in
          while !next < length && is_ascii_ident_char input.[!next] do
            incr next
          done;
          let word = String.sub input index (!next - index) in
          let token =
            match String.lowercase_ascii word with
            | "not" -> TNot
            | "and" -> TAnd
            | "or" -> TOr
            | "forall" -> TForall
            | "exists" -> TExists
            | "in" -> Member
            | "false" -> TBottom
            | _ -> Ident word
          in
          loop !next (token :: tokens)
      | _ -> raise (Parse_error (index, "解釈できない文字です"))
  in
  Array.of_list (loop 0 [])

type state = {
  tokens : token array;
  mutable position : int;
}

let peek state = state.tokens.(state.position)

let take state =
  let token = peek state in
  state.position <- state.position + 1;
  token

let expect state expected message =
  if peek state = expected then ignore (take state)
  else raise (Parse_error (state.position, message))

let expect_ident state =
  match take state with
  | Ident name -> name
  | _ -> raise (Parse_error (state.position, "変数名が必要です"))

let rec parse_formula_state state = parse_iff state

and parse_iff state =
  let left = parse_imp state in
  match peek state with
  | TIff ->
      ignore (take state);
      Iff (left, parse_iff state)
  | _ -> left

and parse_imp state =
  let left = parse_or state in
  match peek state with
  | TImp ->
      ignore (take state);
      Imp (left, parse_imp state)
  | _ -> left

and parse_or state =
  let rec gather left =
    match peek state with
    | TOr ->
        ignore (take state);
        gather (Or (left, parse_and state))
    | _ -> left
  in
  gather (parse_and state)

and parse_and state =
  let rec gather left =
    match peek state with
    | TAnd ->
        ignore (take state);
        gather (And (left, parse_prefix state))
    | _ -> left
  in
  gather (parse_prefix state)

and parse_prefix state =
  match take state with
  | TNot -> Not (parse_prefix state)
  | TForall ->
      let name = expect_ident state in
      expect state Comma "全称量化子の変数の後に , が必要です";
      Forall (name, parse_formula_state state)
  | TExists ->
      let name = expect_ident state in
      expect state Comma "存在量化子の変数の後に , が必要です";
      Exists (name, parse_formula_state state)
  | Lparen ->
      let formula = parse_formula_state state in
      expect state Rparen ") が必要です";
      formula
  | TBottom -> Bottom
  | Ident left ->
      begin
        match peek state with
        | Equal ->
            ignore (take state);
            Eq (left, expect_ident state)
        | NotEqual ->
            ignore (take state);
            Not (Eq (left, expect_ident state))
        | Member ->
            ignore (take state);
            Mem (left, expect_ident state)
        | _ ->
            let rec arguments result =
              match peek state with
              | Ident argument ->
                  ignore (take state);
                  arguments (argument :: result)
              | _ -> List.rev result
            in
            Named (left, arguments [])
      end
  | _ -> raise (Parse_error (state.position, "論理式が必要です"))

let parse_formula input =
  let state = { tokens = lex input; position = 0 } in
  let formula = parse_formula_state state in
  if peek state <> Eof then
    raise (Parse_error
      (state.position, "論理式の後に余分な入力があります"));
  formula

let split_statements script =
  let length = String.length script in
  let buffer = Buffer.create 256 in
  let rec loop index line start_line in_comment statements =
    if index >= length then
      let remaining = String.trim (Buffer.contents buffer) in
      if remaining = "" then List.rev statements
      else
        raise
          (Statement_error
             (Option.value start_line ~default:line,
              "文末に . が必要です"))
    else
      let character = script.[index] in
      if in_comment then
        if character = '\n' then begin
          Buffer.add_char buffer ' ';
          loop (index + 1) (line + 1) start_line false statements
        end else
          loop (index + 1) line start_line true statements
      else
        match character with
        | '#' ->
            loop (index + 1) line start_line true statements
        | '.' ->
            let statement = String.trim (Buffer.contents buffer) in
            Buffer.clear buffer;
            if statement = "" then
              raise (Statement_error (line, "空の文があります"))
            else
              loop (index + 1) line None false
                ((Option.value start_line ~default:line, statement)
                 :: statements)
        | '\n' ->
            Buffer.add_char buffer ' ';
            loop (index + 1) (line + 1) start_line false statements
        | character ->
            let start_line =
              if Option.is_none start_line
                 && character <> ' '
                 && character <> '\t'
                 && character <> '\r'
              then Some line
              else start_line
            in
            Buffer.add_char buffer character;
            loop (index + 1) line start_line false statements
  in
  loop 0 1 None false []
