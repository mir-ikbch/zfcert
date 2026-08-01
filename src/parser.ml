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
  let rec skip_line_comment index =
    if index >= length || input.[index] = '\n' then index
    else skip_line_comment (index + 1)
  in
  let rec skip_block_comment start index depth =
    if index >= length then
      raise (Parse_error (start, "Unterminated block comment."))
    else if starts_with_at input index "(*" then
      skip_block_comment start (index + 2) (depth + 1)
    else if starts_with_at input index "*)" then
      if depth = 1 then index + 2
      else skip_block_comment start (index + 2) (depth - 1)
    else
      skip_block_comment start (index + 1) depth
  in
  let rec loop index tokens =
    if index >= length then List.rev (Eof :: tokens)
    else
      match input.[index] with
      | _ when starts_with_at input index "(*" ->
          loop (skip_block_comment index (index + 2) 1) tokens
      | _ when starts_with_at input index "*)" ->
          raise (Parse_error (index, "Unexpected block comment terminator."))
      | '#' ->
          loop (skip_line_comment (index + 1)) tokens
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
      | _ -> raise (Parse_error (index, "Unrecognized character."))
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

let expect_ident state =
  match take state with
  | Ident name -> name
  | _ -> raise (Parse_error (state.position, "Expected a variable name."))

let rec parse_formula_state state = parse_iff state

and parse_term state =
  match take state with
  | Ident name ->
      begin match peek state with
      | Lparen ->
          ignore (take state);
          let rec arguments accumulated =
            match peek state with
            | Rparen ->
                ignore (take state);
                List.rev accumulated
            | _ ->
                let argument = parse_term state in
                begin match peek state with
                | Comma -> ignore (take state); arguments (argument :: accumulated)
                | Rparen ->
                    ignore (take state);
                    List.rev (argument :: accumulated)
                | _ ->
                    raise (Parse_error
                      (state.position, "Expected a comma or closing parenthesis."))
                end
          in
          App (name, arguments [])
      | _ -> Name name
      end
  | _ -> raise (Parse_error (state.position, "Expected a term."))

and parse_term_tail state name =
  match peek state with
  | Lparen ->
      ignore (take state);
      let rec arguments accumulated =
        match peek state with
        | Rparen ->
            ignore (take state);
            List.rev accumulated
        | _ ->
            let argument = parse_term state in
            begin match peek state with
            | Comma -> ignore (take state); arguments (argument :: accumulated)
            | Rparen ->
                ignore (take state);
                List.rev (argument :: accumulated)
            | _ ->
                raise (Parse_error
                  (state.position, "Expected a comma or closing parenthesis."))
            end
      in
      App (name, arguments [])
  | _ -> Name name

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
      let first = expect_ident state in
      let rec names accumulated =
        match peek state with
        | Ident name ->
            ignore (take state);
            names (name :: accumulated)
        | Comma ->
            ignore (take state);
            let body = parse_formula_state state in
            List.fold_right (fun name body -> Forall (name, body))
              (List.rev accumulated) body
        | _ ->
            raise (Parse_error
              (state.position,
               "Expected a comma after the universally quantified variables."))
      in
      names [first]
  | TExists ->
      let first = expect_ident state in
      let rec names accumulated =
        match peek state with
        | Ident name ->
            ignore (take state);
            names (name :: accumulated)
        | Comma ->
            ignore (take state);
            let body = parse_formula_state state in
            List.fold_right (fun name body -> Exists (name, body))
              (List.rev accumulated) body
        | _ ->
            raise (Parse_error
              (state.position,
               "Expected a comma after the existentially quantified variables."))
      in
      names [first]
  | Lparen ->
      let formula = parse_formula_state state in
      begin match peek state with
      | Rparen -> ignore (take state)
      | Ident _ ->
          raise (Parse_error
            (state.position,
             "Expected ). Function applications use f(a, b), not f a b."))
      | _ -> raise (Parse_error (state.position, "Expected )."))
      end;
      formula
  | TBottom -> Bottom
  | Ident left ->
      let left_term = parse_term_tail state left in
      begin match peek state with
      | Equal ->
          ignore (take state);
          Eq (left_term, parse_term state)
      | NotEqual ->
          ignore (take state);
          Not (Eq (left_term, parse_term state))
      | Member ->
          ignore (take state);
          Mem (left_term, parse_term state)
      | _ ->
          begin match left_term with
          | Name name ->
              let rec arguments result =
                match peek state with
                | Ident argument ->
                    ignore (take state);
                    arguments (argument :: result)
                | _ -> List.rev result
              in
              Named (name, arguments [])
          | App _ ->
              raise (Parse_error
                (state.position, "A function application must be used in a formula."))
          end
      end
  | _ -> raise (Parse_error (state.position, "Expected a formula."))

let parse_formula input =
  let state = { tokens = lex input; position = 0 } in
  let formula = parse_formula_state state in
  if peek state <> Eof then
    begin match peek state with
    | Ident _ ->
        raise (Parse_error
          (state.position,
           "Unexpected term after a formula. Function applications use f(a, b), not f a b."))
    | _ ->
        raise (Parse_error
          (state.position, "Unexpected input after the formula."))
    end;
  formula

let split_statements script =
  let length = String.length script in
  let buffer = Buffer.create 256 in
  let rec loop index line start_line line_comment block_depth
      block_start_line statements =
    if index >= length && block_depth > 0 then
      raise
        (Statement_error
           (Option.value block_start_line ~default:line,
            "Unterminated block comment."))
    else if index >= length then
      let remaining = String.trim (Buffer.contents buffer) in
      if remaining = "" then List.rev statements
      else
        raise
          (Statement_error
             (Option.value start_line ~default:line,
              "Every statement must end with a period."))
    else
      let character = script.[index] in
      if block_depth > 0 then
        if starts_with_at script index "(*" then
          loop (index + 2) line start_line false (block_depth + 1)
            block_start_line statements
        else if starts_with_at script index "*)" then
          loop (index + 2) line start_line false (block_depth - 1)
            (if block_depth = 1 then None else block_start_line)
            statements
        else if character = '\n' then begin
          Buffer.add_char buffer ' ';
          loop (index + 1) (line + 1) start_line false block_depth
            block_start_line statements
        end else
          loop (index + 1) line start_line false block_depth
            block_start_line statements
      else if line_comment then
        if character = '\n' then begin
          Buffer.add_char buffer ' ';
          loop (index + 1) (line + 1) start_line false 0 None statements
        end else
          loop (index + 1) line start_line true 0 None statements
      else
        match character with
        | _ when starts_with_at script index "(*" ->
            Buffer.add_char buffer ' ';
            loop (index + 2) line start_line false 1 (Some line)
              statements
        | _ when starts_with_at script index "*)" ->
            raise
              (Statement_error
                 (line, "Unexpected block comment terminator."))
        | '#' ->
            Buffer.add_char buffer ' ';
            loop (index + 1) line start_line true 0 None statements
        | '.' ->
            let statement = String.trim (Buffer.contents buffer) in
            Buffer.clear buffer;
            if statement = "" then
              raise (Statement_error (line, "Empty statement."))
            else
              loop (index + 1) line None false 0 None
                ((Option.value start_line ~default:line, statement)
                 :: statements)
        | '\n' ->
            Buffer.add_char buffer ' ';
            loop (index + 1) (line + 1) start_line false 0 None statements
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
            loop (index + 1) line start_line false 0 None statements
  in
  loop 0 1 None false 0 None []
