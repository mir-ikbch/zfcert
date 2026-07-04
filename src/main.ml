(* ZFCert: a deliberately small first-order logic kernel and web server. *)

module StringMap = Map.Make (String)
module StringSet = Set.Make (String)
module Verified = Zfcert_kernel

type formula =
  | Bottom
  | Named of string * string list
  | Eq of string * string
  | Mem of string * string
  | Not of formula
  | And of formula * formula
  | Or of formula * formula
  | Imp of formula * formula
  | Iff of formula * formula
  | Forall of string * formula
  | Exists of string * formula

type token =
  | Ident of string
  | Lparen | Rparen | Comma | Colon
  | Equal | NotEqual | Member
  | TNot | TAnd | TOr | TImp | TIff
  | TForall | TExists | TBottom
  | Eof

exception Parse_error of int * string

let starts_with_at s i prefix =
  let n = String.length prefix in
  i + n <= String.length s && String.sub s i n = prefix

let is_ascii_ident_char = function
  | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' -> true
  | _ -> false

let lex input =
  let n = String.length input in
  let rec loop i acc =
    if i >= n then List.rev (Eof :: acc)
    else
      match input.[i] with
      | ' ' | '\t' | '\r' | '\n' -> loop (i + 1) acc
      | '(' -> loop (i + 1) (Lparen :: acc)
      | ')' -> loop (i + 1) (Rparen :: acc)
      | ',' -> loop (i + 1) (Comma :: acc)
      | ':' -> loop (i + 1) (Colon :: acc)
      | '=' -> loop (i + 1) (Equal :: acc)
      | '~' -> loop (i + 1) (TNot :: acc)
      | '&' -> loop (i + 1) (TAnd :: acc)
      | '|' -> loop (i + 1) (TOr :: acc)
      | _ when starts_with_at input i "<->" -> loop (i + 3) (TIff :: acc)
      | _ when starts_with_at input i "->" -> loop (i + 2) (TImp :: acc)
      | _ when starts_with_at input i "!=" -> loop (i + 2) (NotEqual :: acc)
      | _ when starts_with_at input i "⊥" -> loop (i + String.length "⊥") (TBottom :: acc)
      | _ when starts_with_at input i "¬" -> loop (i + String.length "¬") (TNot :: acc)
      | _ when starts_with_at input i "∧" -> loop (i + String.length "∧") (TAnd :: acc)
      | _ when starts_with_at input i "∨" -> loop (i + String.length "∨") (TOr :: acc)
      | _ when starts_with_at input i "→" -> loop (i + String.length "→") (TImp :: acc)
      | _ when starts_with_at input i "↔" -> loop (i + String.length "↔") (TIff :: acc)
      | _ when starts_with_at input i "∈" -> loop (i + String.length "∈") (Member :: acc)
      | _ when starts_with_at input i "∀" -> loop (i + String.length "∀") (TForall :: acc)
      | _ when starts_with_at input i "∃" -> loop (i + String.length "∃") (TExists :: acc)
      | c when is_ascii_ident_char c ->
          let j = ref (i + 1) in
          while !j < n && is_ascii_ident_char input.[!j] do
            incr j
          done;
          let word = String.sub input i (!j - i) in
          let tok =
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
          loop !j (tok :: acc)
      | _ -> raise (Parse_error (i, "解釈できない文字です"))
  in
  Array.of_list (loop 0 [])

type parser = { tokens : token array; mutable pos : int }

let peek p = p.tokens.(p.pos)
let take p = let t = peek p in p.pos <- p.pos + 1; t

let expect p wanted message =
  if peek p = wanted then ignore (take p)
  else raise (Parse_error (p.pos, message))

let expect_ident p =
  match take p with
  | Ident s -> s
  | _ -> raise (Parse_error (p.pos, "変数名が必要です"))

let rec parse_formula_p p = parse_iff p

and parse_iff p =
  let left = parse_imp p in
  match peek p with
  | TIff -> ignore (take p); Iff (left, parse_iff p)
  | _ -> left

and parse_imp p =
  let left = parse_or p in
  match peek p with
  | TImp -> ignore (take p); Imp (left, parse_imp p)
  | _ -> left

and parse_or p =
  let rec gather left =
    match peek p with
    | TOr -> ignore (take p); gather (Or (left, parse_and p))
    | _ -> left
  in
  gather (parse_and p)

and parse_and p =
  let rec gather left =
    match peek p with
    | TAnd -> ignore (take p); gather (And (left, parse_prefix p))
    | _ -> left
  in
  gather (parse_prefix p)

and parse_prefix p =
  match take p with
  | TNot -> Not (parse_prefix p)
  | TForall ->
      let x = expect_ident p in
      expect p Comma "全称量化子の変数の後に , が必要です";
      Forall (x, parse_formula_p p)
  | TExists ->
      let x = expect_ident p in
      expect p Comma "存在量化子の変数の後に , が必要です";
      Exists (x, parse_formula_p p)
  | Lparen ->
      let f = parse_formula_p p in
      expect p Rparen ") が必要です";
      f
  | TBottom -> Bottom
  | Ident x ->
      begin match peek p with
      | Equal -> ignore (take p); Eq (x, expect_ident p)
      | NotEqual -> ignore (take p); Not (Eq (x, expect_ident p))
      | Member -> ignore (take p); Mem (x, expect_ident p)
      | _ ->
          let rec arguments acc =
            match peek p with
            | Ident argument ->
                ignore (take p);
                arguments (argument :: acc)
            | _ -> List.rev acc
          in
          Named (x, arguments [])
      end
  | _ -> raise (Parse_error (p.pos, "論理式が必要です"))

let parse_formula input =
  let p = { tokens = lex input; pos = 0 } in
  let result = parse_formula_p p in
  if peek p <> Eof then raise (Parse_error (p.pos, "論理式の後に余分な入力があります"));
  result

let precedence = function
  | Forall _ | Exists _ -> 0
  | Iff _ -> 1 | Imp _ -> 2 | Or _ -> 3 | And _ -> 4
  | Not _ -> 5
  | Bottom | Named _ | Eq _ | Mem _ -> 6

let rec formula_to_string ?(outer = 0) f =
  let p = precedence f in
  let body =
    match f with
    | Bottom -> "⊥"
    | Named (name, arguments) ->
        String.concat " " (name :: arguments)
    | Eq (a, b) -> a ^ " = " ^ b
    | Mem (a, b) -> a ^ " ∈ " ^ b
    | Not x -> "¬" ^ formula_to_string ~outer:p x
    | And (a, b) ->
        formula_to_string ~outer:p a ^ " ∧ " ^ formula_to_string ~outer:p b
    | Or (a, b) ->
        formula_to_string ~outer:p a ^ " ∨ " ^ formula_to_string ~outer:p b
    | Imp (a, b) ->
        formula_to_string ~outer:(p + 1) a ^ " → " ^ formula_to_string ~outer:p b
    | Iff (a, b) ->
        formula_to_string ~outer:(p + 1) a ^ " ↔ " ^ formula_to_string ~outer:p b
    | Forall (x, body) -> "∀" ^ x ^ ", " ^ formula_to_string ~outer:p body
    | Exists (x, body) -> "∃" ^ x ^ ", " ^ formula_to_string ~outer:p body
  in
  if p < outer then "(" ^ body ^ ")" else body

let rec free_vars = function
  | Bottom -> StringSet.empty
  | Named (_, arguments) -> StringSet.of_list arguments
  | Eq (a, b) | Mem (a, b) -> StringSet.of_list [a; b]
  | Not f -> free_vars f
  | And (a, b) | Or (a, b) | Imp (a, b) | Iff (a, b) ->
      StringSet.union (free_vars a) (free_vars b)
  | Forall (x, f) | Exists (x, f) -> StringSet.remove x (free_vars f)

let rec all_vars = function
  | Bottom -> StringSet.empty
  | Named (_, arguments) -> StringSet.of_list arguments
  | Eq (a, b) | Mem (a, b) -> StringSet.of_list [a; b]
  | Not f -> all_vars f
  | And (a, b) | Or (a, b) | Imp (a, b) | Iff (a, b) ->
      StringSet.union (all_vars a) (all_vars b)
  | Forall (x, f) | Exists (x, f) -> StringSet.add x (all_vars f)

let fresh_name base used =
  let rec try_n n =
    let candidate = if n = 0 then base ^ "'" else base ^ "'" ^ string_of_int n in
    if StringSet.mem candidate used then try_n (n + 1) else candidate
  in
  try_n 0

let rec rename_bound old_name new_name = function
  | Bottom -> Bottom
  | Named (name, arguments) ->
      Named (name,
        List.map
          (fun argument ->
             if argument = old_name then new_name else argument)
          arguments)
  | Eq (a, b) ->
      Eq ((if a = old_name then new_name else a), (if b = old_name then new_name else b))
  | Mem (a, b) ->
      Mem ((if a = old_name then new_name else a), (if b = old_name then new_name else b))
  | Not f -> Not (rename_bound old_name new_name f)
  | And (a, b) -> And (rename_bound old_name new_name a, rename_bound old_name new_name b)
  | Or (a, b) -> Or (rename_bound old_name new_name a, rename_bound old_name new_name b)
  | Imp (a, b) -> Imp (rename_bound old_name new_name a, rename_bound old_name new_name b)
  | Iff (a, b) -> Iff (rename_bound old_name new_name a, rename_bound old_name new_name b)
  | Forall (x, f) when x = old_name -> Forall (x, f)
  | Exists (x, f) when x = old_name -> Exists (x, f)
  | Forall (x, f) -> Forall (x, rename_bound old_name new_name f)
  | Exists (x, f) -> Exists (x, rename_bound old_name new_name f)

let rec subst variable term = function
  | Bottom -> Bottom
  | Named (name, arguments) ->
      Named (name,
        List.map
          (fun argument -> if argument = variable then term else argument)
          arguments)
  | Eq (a, b) ->
      Eq ((if a = variable then term else a), (if b = variable then term else b))
  | Mem (a, b) ->
      Mem ((if a = variable then term else a), (if b = variable then term else b))
  | Not f -> Not (subst variable term f)
  | And (a, b) -> And (subst variable term a, subst variable term b)
  | Or (a, b) -> Or (subst variable term a, subst variable term b)
  | Imp (a, b) -> Imp (subst variable term a, subst variable term b)
  | Iff (a, b) -> Iff (subst variable term a, subst variable term b)
  | Forall (x, f) when x = variable -> Forall (x, f)
  | Exists (x, f) when x = variable -> Exists (x, f)
  | Forall (x, f) when x = term && StringSet.mem variable (free_vars f) ->
      let fresh = fresh_name x (StringSet.add term (all_vars f)) in
      Forall (fresh, subst variable term (rename_bound x fresh f))
  | Exists (x, f) when x = term && StringSet.mem variable (free_vars f) ->
      let fresh = fresh_name x (StringSet.add term (all_vars f)) in
      Exists (fresh, subst variable term (rename_bound x fresh f))
  | Forall (x, f) -> Forall (x, subst variable term f)
  | Exists (x, f) -> Exists (x, subst variable term f)

let alpha_equal left right =
  let rec go env_l env_r next a b =
    let term_equal x y =
      match StringMap.find_opt x env_l, StringMap.find_opt y env_r with
      | Some i, Some j -> i = j
      | None, None -> x = y
      | _ -> false
    in
    match a, b with
    | Bottom, Bottom -> true
    | Named (x, xs), Named (y, ys) ->
        x = y
        && List.length xs = List.length ys
        && List.for_all2 term_equal xs ys
    | Eq (a1, a2), Eq (b1, b2) | Mem (a1, a2), Mem (b1, b2) ->
        term_equal a1 b1 && term_equal a2 b2
    | Not x, Not y -> go env_l env_r next x y
    | And (a1, a2), And (b1, b2)
    | Or (a1, a2), Or (b1, b2)
    | Imp (a1, a2), Imp (b1, b2)
    | Iff (a1, a2), Iff (b1, b2) ->
        go env_l env_r next a1 b1 && go env_l env_r next a2 b2
    | Forall (x, f), Forall (y, g) | Exists (x, f), Exists (y, g) ->
        go (StringMap.add x next env_l) (StringMap.add y next env_r) (next + 1) f g
    | _ -> false
  in
  go StringMap.empty StringMap.empty 0 left right

type axiom = {
  key : string;
  title : string;
  statement : string;
  note : string;
  parsed : formula option;
}

let axiom_data =
  [
    ("empty_set", "空集合",
     "exists e, forall x, not (x in e)",
     "要素を一つも持たない集合が存在する。ZFCでは分出公理図式から導出可能だが、明示的な公理として登録する。");
    ("extensionality", "外延性",
     "forall x, forall y, ((forall z, (z in x <-> z in y)) -> x = y)",
     "同じ要素を持つ集合は等しい。");
    ("pairing", "対集合",
     "forall a, forall b, exists p, forall x, (x in p <-> (x = a or x = b))",
     "任意の二集合から対集合を作れる。");
    ("union", "和集合",
     "forall a, exists u, forall x, (x in u <-> exists y, (x in y and y in a))",
     "集合族の要素を一段平坦化できる。");
    ("power_set", "冪集合",
     "forall a, exists p, forall x, (x in p <-> forall z, (z in x -> z in a))",
     "部分集合全体からなる集合が存在する。");
    ("infinity", "無限",
     "exists i, ((exists e, ((forall z, not (z in e)) and e in i)) and forall x, (x in i -> exists s, (s in i and forall z, (z in s <-> (z in x or z = x)))))",
     "空集合を含み後者操作で閉じた集合が存在する。");
    ("foundation", "正則性",
     "forall x, ((exists a, a in x) -> exists y, (y in x and forall z, (z in y -> not (z in x))))",
     "空でない集合は自身と交わらない要素を持つ。");
    ("separation", "分出公理図式",
     "forall a, exists b, forall x, (x in b <-> (x in a and P))",
     "P は任意の論理式。公理図式なのでテンプレートとして表示する。");
    ("replacement", "置換公理図式",
     "FUNCTIONAL(P) -> forall a, exists b, forall y, (y in b <-> exists x, (x in a and P))",
     "P が関数的である各論理式についての公理図式。");
    ("choice", "選択",
     "forall a, ((forall x, (x in a -> exists y, y in x)) -> exists c, forall x, (x in a -> exists y, ((y in x and y in c) and forall z, ((z in x and z in c) -> z = y))))",
     "非空集合族の各要素からちょうど一つを選ぶ集合が存在する。");
  ]

let axioms =
  List.map
    (fun (key, title, statement, note) ->
       let parsed =
         if key = "separation" || key = "replacement" then None
         else try Some (parse_formula statement) with Parse_error _ -> None
       in
       { key; title; statement; note; parsed })
    axiom_data

let find_axiom name =
  List.find_opt (fun ax -> ax.key = String.lowercase_ascii name) axioms

type display_goal = {
  context : (string * formula) list;
  target : formula;
  environment : string list;
}
type proposition_definition = {
  definition_name : string;
  parameters : string list;
  body : formula;
}

type session = {
  theorem_name : string;
  theorem : formula;
  definitions : proposition_definition list;
  kernel_state : Verified.state;
  display_goals : display_goal list;
  steps : string list;
}

exception Proof_error of int * string

let trim = String.trim

let split_statements script =
  let length = String.length script in
  let buffer = Buffer.create 256 in
  let rec loop index line start_line in_comment statements =
    if index >= length then
      let remaining = trim (Buffer.contents buffer) in
      if remaining = "" then List.rev statements
      else
        raise (Proof_error
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
            let statement = trim (Buffer.contents buffer) in
            Buffer.clear buffer;
            if statement = "" then
              raise (Proof_error (line, "空の文があります"))
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
                 && character <> ' ' && character <> '\t'
                 && character <> '\r'
              then Some line
              else start_line
            in
            Buffer.add_char buffer character;
            loop (index + 1) line start_line false statements
  in
  loop 0 1 None false []

let find_definition name definitions =
  List.find_opt
    (fun definition -> definition.definition_name = name)
    definitions

let substitution_variables substitutions =
  StringMap.fold
    (fun variable term variables ->
       StringSet.add variable (StringSet.add term variables))
    substitutions
    StringSet.empty

let rec subst_many substitutions = function
  | Bottom -> Bottom
  | Named (name, arguments) ->
      Named (name,
        List.map
          (fun argument ->
             Option.value
               (StringMap.find_opt argument substitutions)
               ~default:argument)
          arguments)
  | Eq (a, b) ->
      Eq (Option.value (StringMap.find_opt a substitutions) ~default:a,
          Option.value (StringMap.find_opt b substitutions) ~default:b)
  | Mem (a, b) ->
      Mem (Option.value (StringMap.find_opt a substitutions) ~default:a,
           Option.value (StringMap.find_opt b substitutions) ~default:b)
  | Not f -> Not (subst_many substitutions f)
  | And (a, b) -> And (subst_many substitutions a, subst_many substitutions b)
  | Or (a, b) -> Or (subst_many substitutions a, subst_many substitutions b)
  | Imp (a, b) -> Imp (subst_many substitutions a, subst_many substitutions b)
  | Iff (a, b) -> Iff (subst_many substitutions a, subst_many substitutions b)
  | Forall (x, f) ->
      let substitutions = StringMap.remove x substitutions in
      let captures =
        StringMap.exists
          (fun parameter argument ->
             argument = x && StringSet.mem parameter (free_vars f))
          substitutions
      in
      if captures then
        let used =
          StringSet.union (all_vars f)
            (substitution_variables substitutions)
        in
        let fresh = fresh_name x used in
        Forall (fresh,
          subst_many substitutions (rename_bound x fresh f))
      else
        Forall (x, subst_many substitutions f)
  | Exists (x, f) ->
      let substitutions = StringMap.remove x substitutions in
      let captures =
        StringMap.exists
          (fun parameter argument ->
             argument = x && StringSet.mem parameter (free_vars f))
          substitutions
      in
      if captures then
        let used =
          StringSet.union (all_vars f)
            (substitution_variables substitutions)
        in
        let fresh = fresh_name x used in
        Exists (fresh,
          subst_many substitutions (rename_bound x fresh f))
      else
        Exists (x, subst_many substitutions f)

let rec unfold_formula line_no definitions visiting = function
  | Named (name, arguments) ->
      if StringSet.mem name visiting then
        raise (Proof_error (line_no, "定義 " ^ name ^ " が循環しています"));
      begin match find_definition name definitions with
      | Some definition ->
          let expected = List.length definition.parameters in
          let actual = List.length arguments in
          if expected <> actual then
            raise (Proof_error (line_no,
              Printf.sprintf
                "定義 %s の引数は %d 個必要ですが、%d 個与えられています"
                name expected actual));
          let substitutions =
            List.fold_left2
              (fun substitutions parameter argument ->
                 StringMap.add parameter argument substitutions)
              StringMap.empty definition.parameters arguments
          in
          let instantiated = subst_many substitutions definition.body in
          unfold_formula line_no definitions
            (StringSet.add name visiting) instantiated
      | None -> raise (Proof_error (line_no, "未定義の命題名です: " ^ name))
      end
  | Bottom -> Bottom
  | Eq (a, b) -> Eq (a, b)
  | Mem (a, b) -> Mem (a, b)
  | Not f -> Not (unfold_formula line_no definitions visiting f)
  | And (a, b) ->
      And (unfold_formula line_no definitions visiting a,
           unfold_formula line_no definitions visiting b)
  | Or (a, b) ->
      Or (unfold_formula line_no definitions visiting a,
          unfold_formula line_no definitions visiting b)
  | Imp (a, b) ->
      Imp (unfold_formula line_no definitions visiting a,
           unfold_formula line_no definitions visiting b)
  | Iff (a, b) ->
      Iff (unfold_formula line_no definitions visiting a,
           unfold_formula line_no definitions visiting b)
  | Forall (x, f) ->
      Forall (x, unfold_formula line_no definitions visiting f)
  | Exists (x, f) ->
      Exists (x, unfold_formula line_no definitions visiting f)

let unfold line_no definitions formula =
  unfold_formula line_no definitions StringSet.empty formula

let split_first_word line =
  match String.index_opt line ' ' with
  | None -> (line, "")
  | Some i -> (String.sub line 0 i, trim (String.sub line (i + 1) (String.length line - i - 1)))

let split_schema_argument line_no definitions argument =
  match String.index_opt argument ':' with
  | None -> raise (Proof_error (line_no, "公理図式の指定には : が必要です"))
  | Some i ->
      let names =
        String.sub argument 0 i
        |> trim
        |> String.split_on_char ' '
        |> List.map trim
        |> List.filter (fun name -> name <> "")
      in
      let statement = trim (String.sub argument (i + 1) (String.length argument - i - 1)) in
      if statement = "" then raise (Proof_error (line_no, ": の後に論理式が必要です"));
      let predicate =
        try parse_formula statement |> unfold line_no definitions
        with Parse_error (_, message) -> raise (Proof_error (line_no, message))
      in
      (names, predicate)

let context_free_vars context =
  List.fold_left (fun acc (_, f) -> StringSet.union acc (free_vars f)) StringSet.empty context

(** Boundary between the user-facing named syntax and the extracted,
    de Bruijn-indexed proof-state kernel. *)

let rec list_index name index = function
  | [] -> None
  | item :: _ when item = name -> Some index
  | _ :: rest -> list_index name (index + 1) rest

let add_free_name environment name =
  if List.mem name environment then environment else environment @ [name]

let canonical_environment goal =
  goal.environment

let db_variable bound environment name =
  match list_index name 0 bound with
  | Some index -> index
  | None ->
      begin match list_index name 0 environment with
      | Some index -> List.length bound + index
      | None ->
          raise (Proof_error (1,
            "内部検証で自由変数 " ^ name ^ " の番号付けに失敗しました"))
      end

let rec db_formula bound environment = function
  | Bottom -> Verified.Falsum
  | Named (name, _) ->
      raise (Proof_error (1,
        "内部検証へ未展開の定義 " ^ name ^ " が渡されました"))
  | Eq (a, b) ->
      Verified.Equal
        (db_variable bound environment a, db_variable bound environment b)
  | Mem (a, b) ->
      Verified.Member
        (db_variable bound environment a, db_variable bound environment b)
  | Not f -> Verified.Impl (db_formula bound environment f, Verified.Falsum)
  | And (a, b) ->
      Verified.Conj
        (db_formula bound environment a, db_formula bound environment b)
  | Or (a, b) ->
      Verified.Disj
        (db_formula bound environment a, db_formula bound environment b)
  | Imp (a, b) ->
      Verified.Impl
        (db_formula bound environment a, db_formula bound environment b)
  | Iff (a, b) ->
      let left = db_formula bound environment a in
      let right = db_formula bound environment b in
      Verified.Conj
        (Verified.Impl (left, right), Verified.Impl (right, left))
  | Forall (x, body) ->
      Verified.All (db_formula (x :: bound) environment body)
  | Exists (x, body) ->
      Verified.Ex (db_formula (x :: bound) environment body)

let db_goal environment goal =
  {
    Verified.assumptions =
      List.map (fun (_, f) -> db_formula [] environment f) goal.context;
    Verified.conclusion = db_formula [] environment goal.target;
  }

let db_goal_canonical goal = db_goal (canonical_environment goal) goal

let verified_error line =
  raise (Proof_error (line,
    "抽出済みCoqカーネルがタクティク遷移を拒否しました"))

let verify_user_transition line command kernel_state rest generated
    before_environment generated_environment =
  let expected =
    List.map (db_goal generated_environment) generated @
    List.map db_goal_canonical rest
  in
  ignore before_environment;
  match Verified.step command kernel_state with
  | Ok next when Verified.goals next = expected -> next
  | Ok _ | Error _ -> verified_error line

let verify_rule_transition_with_environments line axioms rules kernel_state
    rest generated before_environment =
  let expected =
    List.map (fun (goal, environment) -> db_goal environment goal) generated @
    List.map db_goal_canonical rest
  in
  ignore before_environment;
  match Verified.rule_run ~axioms rules kernel_state with
  | Ok next when Verified.goals next = expected -> next
  | Ok _ | Error _ -> verified_error line

let verify_rule_transition line axioms rules kernel_state rest generated
    before_environment generated_environment =
  verify_rule_transition_with_environments line axioms rules kernel_state rest
    (List.map (fun goal -> (goal, generated_environment)) generated)
    before_environment

let context_index name context =
  let rec loop index = function
    | [] -> None
    | (label, _) :: _ when label = name -> Some index
    | _ :: rest -> loop (index + 1) rest
  in
  loop 0 context

let lookup_fact name context =
  match List.assoc_opt name context with
  | Some f -> Some f
  | None ->
      begin match find_axiom name with
      | Some { parsed = Some f; _ } -> Some f
      | _ -> None
      end

let rec instantiate_formula substitutions = function
  | Bottom -> Bottom
  | Named (name, arguments) ->
      Named (name,
        List.map
          (fun argument ->
             Option.value
               (StringMap.find_opt argument substitutions)
               ~default:argument)
          arguments)
  | Eq (a, b) ->
      Eq (Option.value (StringMap.find_opt a substitutions) ~default:a,
          Option.value (StringMap.find_opt b substitutions) ~default:b)
  | Mem (a, b) ->
      Mem (Option.value (StringMap.find_opt a substitutions) ~default:a,
           Option.value (StringMap.find_opt b substitutions) ~default:b)
  | Not f -> Not (instantiate_formula substitutions f)
  | And (a, b) -> And (instantiate_formula substitutions a, instantiate_formula substitutions b)
  | Or (a, b) -> Or (instantiate_formula substitutions a, instantiate_formula substitutions b)
  | Imp (a, b) -> Imp (instantiate_formula substitutions a, instantiate_formula substitutions b)
  | Iff (a, b) -> Iff (instantiate_formula substitutions a, instantiate_formula substitutions b)
  | Forall (x, f) ->
      Forall (x, instantiate_formula (StringMap.remove x substitutions) f)
  | Exists (x, f) ->
      Exists (x, instantiate_formula (StringMap.remove x substitutions) f)

let match_formula metas pattern actual =
  let term active_metas sub p a =
    if StringSet.mem p active_metas then
      match StringMap.find_opt p sub with
      | None -> Some (StringMap.add p a sub)
      | Some old when old = a -> Some sub
      | Some _ -> None
    else if p = a then Some sub else None
  in
  let rec go active_metas sub p a =
    match p, a with
    | Bottom, Bottom -> Some sub
    | Named (p, ps), Named (a, actuals)
      when p = a && ps = actuals -> Some sub
    | Eq (p1, p2), Eq (a1, a2) | Mem (p1, p2), Mem (a1, a2) ->
        Option.bind (term active_metas sub p1 a1)
          (fun sub' -> term active_metas sub' p2 a2)
    | Not p, Not a -> go active_metas sub p a
    | And (p1, p2), And (a1, a2)
    | Or (p1, p2), Or (a1, a2)
    | Imp (p1, p2), Imp (a1, a2)
    | Iff (p1, p2), Iff (a1, a2) ->
        Option.bind (go active_metas sub p1 a1)
          (fun sub' -> go active_metas sub' p2 a2)
    | Forall (x, p), Forall (y, a) | Exists (x, p), Exists (y, a) ->
        let p' = if x = y then p else subst x y p in
        go (StringSet.remove x active_metas) sub p' a
    | _ -> None
  in
  go metas StringMap.empty pattern actual

let decompose_forall formula =
  let rec loop metas = function
    | Forall (x, body) -> loop (StringSet.add x metas) body
    | f -> (metas, f)
  in
  loop StringSet.empty formula

let decompose_imp formula =
  let rec loop premises = function
    | Imp (a, b) -> loop (a :: premises) b
    | Not a -> (List.rev (a :: premises), Bottom)
    | f -> (List.rev premises, f)
  in
  loop [] formula

let apply_fact fact goal =
  let metas, body = decompose_forall fact in
  let premises, conclusion = decompose_imp body in
  match match_formula metas conclusion goal.target with
  | None -> Error "この事実の結論は現在のゴールと一致しません"
  | Some sub ->
      let premises = List.map (instantiate_formula sub) premises in
      Ok (List.map
        (fun target ->
           { context = goal.context;
             target;
             environment = goal.environment;
           })
        premises, sub)

let add_step state text goals kernel_state =
  { state with
    kernel_state;
    display_goals = goals;
    steps = state.steps @ [text];
  }

let apply_user_transition line_no state command text generated rest
    before_environment generated_environment =
  let generated =
    List.map
      (fun goal -> { goal with environment = generated_environment })
      generated
  in
  let kernel_state =
    verify_user_transition line_no command state.kernel_state
      rest generated before_environment generated_environment
  in
  add_step state text (generated @ rest) kernel_state

let apply_rule_transition line_no state axioms rules text generated rest
    before_environment generated_environment =
  let generated =
    List.map
      (fun goal -> { goal with environment = generated_environment })
      generated
  in
  let kernel_state =
    verify_rule_transition line_no axioms rules state.kernel_state
      rest generated before_environment generated_environment
  in
  add_step state text (generated @ rest) kernel_state

let words text =
  text
  |> String.split_on_char ' '
  |> List.map trim
  |> List.filter (fun word -> word <> "")

let parse_formula_at line_no definitions text =
  try parse_formula (trim text) |> unfold line_no definitions
  with Parse_error (_, message) -> raise (Proof_error (line_no, message))

let split_rule_formula line_no argument =
  match String.index_opt argument ':' with
  | None ->
      raise (Proof_error (line_no,
        "この推論規則では : の後に論理式を指定します"))
  | Some index ->
      let parameters = trim (String.sub argument 0 index) in
      let formula =
        trim (String.sub argument (index + 1)
          (String.length argument - index - 1))
      in
      if formula = "" then
        raise (Proof_error (line_no, ": の後に論理式が必要です"));
      (words parameters, formula)

let extend_environment environment formula =
  StringSet.fold (fun name result -> add_free_name result name)
    (free_vars formula) environment

let body_db line_no environment binder body =
  match db_formula [] environment (Forall (binder, body)) with
  | Verified.All primitive_body -> primitive_body
  | _ -> verified_error line_no

let separation_instance source element predicate =
  let used =
    all_vars predicate
    |> StringSet.add source
    |> StringSet.add element
  in
  let subset = fresh_name "b" used in
  Exists (subset,
    Forall (element,
      Iff (Mem (element, subset),
        And (Mem (element, source), predicate))))

let replacement_instance source input output predicate =
  let used =
    all_vars predicate
    |> StringSet.add source
    |> StringSet.add input
    |> StringSet.add output
  in
  let alternate = fresh_name "z" used in
  let image_set = fresh_name "b" (StringSet.add alternate used) in
  let alternate_predicate = subst output alternate predicate in
  let functional =
    Forall (input,
      Exists (output,
        And (predicate,
          Forall (alternate,
            Imp (alternate_predicate, Eq (alternate, output))))))
  in
  let image =
    Exists (image_set,
      Forall (output,
        Iff (Mem (output, image_set),
          Exists (input,
            And (Mem (input, source), predicate)))))
  in
  Imp (functional, image)

let fixed_axiom_kind = function
  | "empty_set" -> Some Verified.EmptySet
  | "extensionality" -> Some Verified.Extensionality
  | "pairing" -> Some Verified.Pairing
  | "union" -> Some Verified.Union
  | "power_set" -> Some Verified.PowerSet
  | "foundation" -> Some Verified.Foundation
  | "infinity" -> Some Verified.Infinity
  | "choice" -> Some Verified.Choice
  | _ -> None

let local_predicate_db environment binders predicate =
  let parameters =
    List.filter (fun name -> not (List.mem name binders)) environment
  in
  db_formula binders parameters predicate

let execute_rule line_no state argument =
  match state.display_goals with
  | [] -> raise (Proof_error (line_no, "証明はすでに完了しています"))
  | goal :: rest ->
      let rule_name, rule_argument = split_first_word argument in
      let rule_name = String.lowercase_ascii rule_name in
      let finish ?(axioms = []) primitive generated
          before_environment generated_environment description =
        apply_rule_transition line_no state axioms [primitive]
          ("rule " ^ description) generated rest
          before_environment generated_environment
      in
      begin match rule_name with
      | "axiom" ->
          let axiom, rules =
            if trim rule_argument = "" then
              let matching =
                List.find_opt
                  (fun axiom ->
                     match axiom.parsed with
                     | Some formula -> alpha_equal formula goal.target
                     | None -> false)
                  axioms
              in
              begin match matching with
              | Some axiom ->
                  begin match fixed_axiom_kind axiom.key with
                  | Some kind ->
                      (Verified.fixed_axiom kind, [Verified.RAxiom])
                  | None -> verified_error line_no
                  end
              | None ->
                  raise (Proof_error (line_no,
                    "現在のゴールは登録済みの公理ではありません"))
              end
            else
              let schema, schema_argument =
                split_first_word rule_argument
              in
              let names, predicate =
                split_schema_argument line_no state.definitions
                  schema_argument
              in
              let instance, axiom, rules =
                match String.lowercase_ascii schema, names with
                | "separation", [source; element] ->
                    let instance =
                      separation_instance source element predicate
                    in
                    let environment =
                      add_free_name (canonical_environment goal) source
                    in
                    let predicate_db =
                      local_predicate_db environment
                        [element; source] predicate
                    in
                    let full =
                      Verified.separation_instance predicate_db
                    in
                    let body =
                      match full with
                      | Verified.All body -> body
                      | _ -> verified_error line_no
                    in
                    let source_index =
                      Option.get (list_index source 0 environment)
                    in
                    (instance,
                     Verified.separation_axiom predicate_db,
                     [Verified.RAllElim (body, source_index);
                      Verified.RAxiom])
                | "replacement", [source; input; output] ->
                    let instance =
                      replacement_instance source input output predicate
                    in
                    let environment =
                      add_free_name (canonical_environment goal) source
                    in
                    let predicate_db =
                      local_predicate_db environment
                        [output; input] predicate
                    in
                    let full =
                      Verified.replacement_instance predicate_db
                    in
                    let functional, image_body =
                      match full with
                      | Verified.Impl
                          (functional, Verified.All image_body) ->
                          (functional, image_body)
                      | _ -> verified_error line_no
                    in
                    let source_index =
                      Option.get (list_index source 0 environment)
                    in
                    (instance,
                     Verified.replacement_axiom predicate_db,
                     [Verified.RImplIntro;
                      Verified.RAllElim (image_body, source_index);
                      Verified.RImplElim functional;
                      Verified.RAxiom;
                      Verified.RHypothesis 0])
                | "separation", _ ->
                    raise (Proof_error (line_no,
                      "rule axiom separation source x : P の形で指定します"))
                | "replacement", _ ->
                    raise (Proof_error (line_no,
                      "rule axiom replacement source x y : P の形で指定します"))
                | _ ->
                    raise (Proof_error (line_no,
                      "rule axiom の引数には separation または replacement を指定します"))
              in
              if not (alpha_equal instance goal.target) then
                raise (Proof_error (line_no,
                  "指定した公理図式は現在のゴールと一致しません"));
              (axiom, rules)
          in
          let environment = canonical_environment goal in
          let kernel_state =
            verify_rule_transition line_no [axiom] rules
              state.kernel_state rest []
              environment environment
          in
          add_step state "rule axiom" rest kernel_state
      | "hypothesis" ->
          let name = trim rule_argument in
          begin match context_index name goal.context with
          | None ->
              raise (Proof_error (line_no, "仮定 " ^ name ^ " が見つかりません"))
          | Some index ->
              let environment = canonical_environment goal in
              finish (Verified.RHypothesis index) []
                environment environment ("hypothesis " ^ name)
          end
      | "falsum_elim" ->
          if trim rule_argument <> "" then
            raise (Proof_error (line_no,
              "rule falsum_elim に引数はありません"));
          let next = { goal with target = Bottom } in
          let environment = canonical_environment goal in
          finish Verified.RFalsumElim [next]
            environment environment "falsum_elim"
      | "impl_intro" ->
          begin match goal.target with
          | Imp (premise, target) ->
              let name = trim rule_argument in
              if name = "" then
                raise (Proof_error (line_no,
                  "rule impl_intro H の形で仮定名を指定します"));
              if List.mem_assoc name goal.context then
                raise (Proof_error (line_no,
                  "同じ名前の仮定がすでにあります"));
              let next = {
                context = (name, premise) :: goal.context;
                target;
                environment = goal.environment;
              } in
              let environment = canonical_environment goal in
              finish Verified.RImplIntro [next]
                environment environment ("impl_intro " ^ name)
          | _ ->
              raise (Proof_error (line_no,
                "rule impl_intro は含意のゴールに使います"))
          end
      | "impl_elim" ->
          let _, formula_text = split_rule_formula line_no rule_argument in
          let premise =
            parse_formula_at line_no state.definitions formula_text
          in
          let generated = [
            { goal with target = Imp (premise, goal.target) };
            { goal with target = premise };
          ] in
          let environment =
            extend_environment (canonical_environment goal) premise
          in
          let premise_db = db_formula [] environment premise in
          finish (Verified.RImplElim premise_db) generated
            environment environment "impl_elim"
      | "conj_intro" ->
          begin match goal.target with
          | And (left, right) ->
              let environment = canonical_environment goal in
              finish Verified.RConjIntro
                [{ goal with target = left }; { goal with target = right }]
                environment environment "conj_intro"
          | _ ->
              raise (Proof_error (line_no,
                "rule conj_intro は連言のゴールに使います"))
          end
      | "conj_elim_l" ->
          let _, formula_text = split_rule_formula line_no rule_argument in
          let right =
            parse_formula_at line_no state.definitions formula_text
          in
          let next = { goal with target = And (goal.target, right) } in
          let environment =
            extend_environment (canonical_environment goal) right
          in
          finish (Verified.RConjElimL (db_formula [] environment right))
            [next] environment environment "conj_elim_l"
      | "conj_elim_r" ->
          let _, formula_text = split_rule_formula line_no rule_argument in
          let left =
            parse_formula_at line_no state.definitions formula_text
          in
          let next = { goal with target = And (left, goal.target) } in
          let environment =
            extend_environment (canonical_environment goal) left
          in
          finish (Verified.RConjElimR (db_formula [] environment left))
            [next] environment environment "conj_elim_r"
      | "disj_intro_l" ->
          begin match goal.target with
          | Or (left, _) ->
              let environment = canonical_environment goal in
              finish Verified.RDisjIntroL [{ goal with target = left }]
                environment environment "disj_intro_l"
          | _ ->
              raise (Proof_error (line_no,
                "rule disj_intro_l は選言のゴールに使います"))
          end
      | "disj_intro_r" ->
          begin match goal.target with
          | Or (_, right) ->
              let environment = canonical_environment goal in
              finish Verified.RDisjIntroR [{ goal with target = right }]
                environment environment "disj_intro_r"
          | _ ->
              raise (Proof_error (line_no,
                "rule disj_intro_r は選言のゴールに使います"))
          end
      | "disj_elim" ->
          let names, formulas = split_rule_formula line_no rule_argument in
          let left_name, right_name =
            match names with
            | [left_name; right_name] -> (left_name, right_name)
            | _ ->
                raise (Proof_error (line_no,
                  "rule disj_elim HL HR : P ; Q の形で指定します"))
          in
          let separator =
            match String.index_opt formulas ';' with
            | Some index -> index
            | None ->
                raise (Proof_error (line_no,
                  "二つの論理式を ; で区切ります"))
          in
          let left =
            String.sub formulas 0 separator
            |> parse_formula_at line_no state.definitions
          in
          let right =
            String.sub formulas (separator + 1)
              (String.length formulas - separator - 1)
            |> parse_formula_at line_no state.definitions
          in
          if List.mem_assoc left_name goal.context
             || List.mem_assoc right_name goal.context then
            raise (Proof_error (line_no,
              "分岐の仮定名には未使用の名前を指定します"));
          let generated = [
            { goal with target = Or (left, right) };
            { context = (left_name, left) :: goal.context;
              target = goal.target;
              environment = goal.environment };
            { context = (right_name, right) :: goal.context;
              target = goal.target;
              environment = goal.environment };
          ] in
          let environment =
            canonical_environment goal
            |> fun result -> extend_environment result left
            |> fun result -> extend_environment result right
          in
          finish
            (Verified.RDisjElim
              (db_formula [] environment left,
               db_formula [] environment right))
            generated environment environment "disj_elim"
      | "all_intro" ->
          begin match goal.target with
          | Forall (bound, body) ->
              let chosen =
                let name = trim rule_argument in
                if name = "" then bound else name
              in
              if StringSet.mem chosen (context_free_vars goal.context) then
                raise (Proof_error (line_no,
                  "全称導入する変数が仮定中で自由に現れています"));
              let next = { goal with target = subst bound chosen body } in
              let before_environment = canonical_environment goal in
              let generated_environment =
                chosen :: before_environment
              in
              finish Verified.RAllIntro [next]
                before_environment generated_environment
                ("all_intro " ^ chosen)
          | _ ->
              raise (Proof_error (line_no,
                "rule all_intro は全称量化のゴールに使います"))
          end
      | "all_elim" ->
          let parameters, formula_text =
            split_rule_formula line_no rule_argument
          in
          let term, binder =
            match parameters with
            | [term; binder] -> (term, binder)
            | _ ->
                raise (Proof_error (line_no,
                  "rule all_elim term x : P の形で指定します"))
          in
          let body =
            parse_formula_at line_no state.definitions formula_text
          in
          let universal = Forall (binder, body) in
          let environment =
            extend_environment (canonical_environment goal) universal
            |> fun result -> add_free_name result term
          in
          let term_index =
            Option.get (list_index term 0 environment)
          in
          let primitive_body = body_db line_no environment binder body in
          finish (Verified.RAllElim (primitive_body, term_index))
            [{ goal with target = universal }]
            environment environment "all_elim"
      | "ex_intro" ->
          begin match goal.target with
          | Exists (bound, body) ->
              let term = trim rule_argument in
              if term = "" then
                raise (Proof_error (line_no,
                  "rule ex_intro term の形で証人を指定します"));
              let environment =
                add_free_name (canonical_environment goal) term
              in
              let term_index =
                Option.get (list_index term 0 environment)
              in
              finish (Verified.RExIntro term_index)
                [{ goal with target = subst bound term body }]
                environment environment ("ex_intro " ^ term)
          | _ ->
              raise (Proof_error (line_no,
                "rule ex_intro は存在量化のゴールに使います"))
          end
      | "ex_elim" ->
          let parameters, formula_text =
            split_rule_formula line_no rule_argument
          in
          let witness, hypothesis =
            match parameters with
            | [witness; hypothesis] -> (witness, hypothesis)
            | _ ->
                raise (Proof_error (line_no,
                  "rule ex_elim x H : P の形で指定します"))
          in
          let forbidden =
            StringSet.union (context_free_vars goal.context)
              (free_vars goal.target)
          in
          if StringSet.mem witness forbidden then
            raise (Proof_error (line_no,
              "存在除去の変数は文脈とゴールに現れない名前にします"));
          if List.mem_assoc hypothesis goal.context then
            raise (Proof_error (line_no,
              "存在除去の仮定名には未使用の名前を指定します"));
          let body =
            parse_formula_at line_no state.definitions formula_text
          in
          let existential = Exists (witness, body) in
          let first = { goal with target = existential } in
          let second = {
            context = (hypothesis, body) :: goal.context;
            target = goal.target;
            environment = goal.environment;
          } in
          let before_environment =
            extend_environment (canonical_environment goal) existential
          in
          let generated_environment =
            witness :: before_environment
          in
          let first = {
            first with environment = before_environment;
          } in
          let second = {
            second with environment = generated_environment;
          } in
          let primitive_body =
            body_db line_no before_environment witness body
          in
          let kernel_state =
            verify_rule_transition_with_environments line_no
              [] [Verified.RExElim primitive_body]
              state.kernel_state rest
              [(first, before_environment);
               (second, generated_environment)]
              before_environment
          in
          add_step state "rule ex_elim"
            (first :: second :: rest) kernel_state
      | "equal_refl" ->
          begin match goal.target with
          | Eq (left, right) when left = right ->
              let environment = canonical_environment goal in
              finish Verified.REqualRefl []
                environment environment "equal_refl"
          | _ ->
              raise (Proof_error (line_no,
                "rule equal_refl は t = t のゴールに使います"))
          end
      | "equal_elim" ->
          let parameters, formula_text =
            split_rule_formula line_no rule_argument
          in
          let left, right, binder =
            match parameters with
            | [left; right; binder] -> (left, right, binder)
            | _ ->
                raise (Proof_error (line_no,
                  "rule equal_elim s t x : P の形で指定します"))
          in
          let predicate =
            parse_formula_at line_no state.definitions formula_text
          in
          let quantified = Forall (binder, predicate) in
          let environment =
            extend_environment (canonical_environment goal) quantified
            |> fun result -> add_free_name result left
            |> fun result -> add_free_name result right
          in
          let left_index =
            Option.get (list_index left 0 environment)
          in
          let right_index =
            Option.get (list_index right 0 environment)
          in
          let primitive_predicate =
            body_db line_no environment binder predicate
          in
          let generated = [
            { goal with target = Eq (left, right) };
            { goal with target = subst binder left predicate };
          ] in
          finish
            (Verified.REqualElim
              (primitive_predicate, left_index, right_index))
            generated environment environment "equal_elim"
      | "cut" ->
          let names, formula_text =
            split_rule_formula line_no rule_argument
          in
          let hypothesis =
            match names with
            | [name] -> name
            | _ ->
                raise (Proof_error (line_no,
                  "rule cut H : P の形で指定します"))
          in
          if List.mem_assoc hypothesis goal.context then
            raise (Proof_error (line_no,
              "カットで導入する仮定名には未使用の名前を指定します"));
          let lemma =
            parse_formula_at line_no state.definitions formula_text
          in
          let generated = [
            { goal with target = lemma };
            { context = (hypothesis, lemma) :: goal.context;
              target = goal.target;
              environment = goal.environment };
          ] in
          let environment =
            extend_environment (canonical_environment goal) lemma
          in
          finish (Verified.RCut (db_formula [] environment lemma))
            generated environment environment "cut"
      | "" ->
          raise (Proof_error (line_no, "rule の名前が必要です"))
      | unknown ->
          raise (Proof_error (line_no,
            "未知の推論規則です: " ^ unknown))
      end

let execute_tactic line_no state line =
  match state.display_goals with
  | [] -> raise (Proof_error (line_no, "証明はすでに完了しています"))
  | goal :: rest ->
      let command, argument = split_first_word line in
      let command = String.lowercase_ascii command in
      begin match command with
      | "rule" -> execute_rule line_no state argument
      | "separation" ->
          let names, predicate =
            split_schema_argument line_no state.definitions argument
          in
          begin match names with
          | [fact_name; source; element] ->
              if List.mem_assoc fact_name goal.context then
                raise (Proof_error (line_no, "同じ名前の事実がすでにあります"));
              if source = element then
                raise (Proof_error (line_no, "母集合と要素変数には異なる名前を使います"));
              let used =
                all_vars predicate
                |> StringSet.add source
                |> StringSet.add element
              in
              let subset = fresh_name "b" used in
              let instance =
                Exists (subset,
                  Forall (element,
                    Iff (Mem (element, subset),
                      And (Mem (element, source), predicate))))
              in
              let next = { goal with context = (fact_name, instance) :: goal.context } in
              let environment =
                StringSet.fold (fun name env -> add_free_name env name)
                  (free_vars instance)
                  (canonical_environment goal)
              in
              let next = { next with environment } in
              let instance_db = db_formula [] environment instance in
              let predicate_db =
                local_predicate_db environment
                  [element; source] predicate
              in
              let full =
                Verified.separation_instance predicate_db
              in
              let body =
                match full with
                | Verified.All body -> body
                | _ -> verified_error line_no
              in
              let source_index =
                Option.get (list_index source 0 environment)
              in
              let kernel_state =
                verify_rule_transition line_no
                  [Verified.separation_axiom predicate_db]
                  [Verified.RCut instance_db;
                   Verified.RAllElim (body, source_index);
                   Verified.RAxiom]
                  state.kernel_state rest [next]
                  environment environment
              in
              add_step state ("separation " ^ fact_name)
                (next :: rest) kernel_state
          | _ ->
              raise (Proof_error (line_no,
                "separation S source x : P の形で指定します"))
          end
      | "replacement" ->
          let names, predicate =
            split_schema_argument line_no state.definitions argument
          in
          begin match names with
          | [fact_name; source; input; output] ->
              if List.mem_assoc fact_name goal.context then
                raise (Proof_error (line_no, "同じ名前の事実がすでにあります"));
              if source = input || input = output || source = output then
                raise (Proof_error (line_no, "母集合・入力・出力変数には異なる名前を使います"));
              let used =
                all_vars predicate
                |> StringSet.add source
                |> StringSet.add input
                |> StringSet.add output
              in
              let alternate = fresh_name "z" used in
              let image_set = fresh_name "b" (StringSet.add alternate used) in
              let alternate_predicate = subst output alternate predicate in
              let functional =
                Forall (input,
                  Exists (output,
                    And (predicate,
                      Forall (alternate,
                        Imp (alternate_predicate, Eq (alternate, output))))))
              in
              let image =
                Exists (image_set,
                  Forall (output,
                    Iff (Mem (output, image_set),
                      Exists (input,
                        And (Mem (input, source), predicate)))))
              in
              let instance = Imp (functional, image) in
              let next = { goal with context = (fact_name, instance) :: goal.context } in
              let environment =
                StringSet.fold (fun name env -> add_free_name env name)
                  (free_vars instance)
                  (canonical_environment goal)
              in
              let next = { next with environment } in
              let instance_db = db_formula [] environment instance in
              let predicate_db =
                local_predicate_db environment
                  [output; input] predicate
              in
              let full =
                Verified.replacement_instance predicate_db
              in
              let functional_db, image_body =
                match full with
                | Verified.Impl
                    (functional, Verified.All image_body) ->
                    (functional, image_body)
                | _ -> verified_error line_no
              in
              let source_index =
                Option.get (list_index source 0 environment)
              in
              let kernel_state =
                verify_rule_transition line_no
                  [Verified.replacement_axiom predicate_db]
                  [Verified.RCut instance_db;
                   Verified.RImplIntro;
                   Verified.RAllElim (image_body, source_index);
                   Verified.RImplElim functional_db;
                   Verified.RAxiom;
                   Verified.RHypothesis 0]
                  state.kernel_state rest [next]
                  environment environment
              in
              add_step state ("replacement " ^ fact_name)
                (next :: rest) kernel_state
          | _ ->
              raise (Proof_error (line_no,
                "replacement R source x y : P の形で指定します"))
          end
      | "intro" ->
          begin match goal.target with
          | Imp (premise, target) ->
              if argument = "" then raise (Proof_error (line_no, "仮定の名前が必要です"));
              if List.mem_assoc argument goal.context then
                raise (Proof_error (line_no, "同じ名前の仮定がすでにあります"));
              let next = {
                context = (argument, premise) :: goal.context;
                target;
                environment = goal.environment;
              } in
              let environment = canonical_environment goal in
              apply_user_transition line_no state Verified.TacIntro
                ("intro " ^ argument) [next] rest
                environment environment
          | Forall (x, body) ->
              let chosen = if argument = "" then x else argument in
              if StringSet.mem chosen (context_free_vars goal.context) then
                raise (Proof_error (line_no, "全称導入する変数が仮定中で自由に現れています"));
              let next = { goal with target = subst x chosen body } in
              let before_environment = canonical_environment goal in
              let generated_environment = chosen :: before_environment in
              apply_user_transition line_no state Verified.TacIntro
                ("intro " ^ chosen) [next] rest
                before_environment generated_environment
          | Not premise ->
              if argument = "" then raise (Proof_error (line_no, "仮定の名前が必要です"));
              if List.mem_assoc argument goal.context then
                raise (Proof_error (line_no, "同じ名前の仮定がすでにあります"));
              let next = {
                context = (argument, premise) :: goal.context;
                target = Bottom;
                environment = goal.environment;
              } in
              let environment = canonical_environment goal in
              apply_user_transition line_no state Verified.TacIntro
                ("intro " ^ argument) [next] rest
                environment environment
          | _ -> raise (Proof_error (line_no, "intro は含意・否定・全称量化のゴールに使います"))
          end
      | "assumption" ->
          let rec find index = function
            | [] -> None
            | (_, f) :: _ when alpha_equal f goal.target -> Some index
            | _ :: tail -> find (index + 1) tail
          in
          begin match find 0 goal.context with
          | Some index ->
              let environment = canonical_environment goal in
              apply_user_transition line_no state
                (Verified.TacExact index) "assumption" [] rest
                environment environment
          | None ->
              raise (Proof_error (line_no, "現在のゴールと一致する仮定がありません"))
          end
      | "exact" ->
          begin match lookup_fact argument goal.context with
          | None -> raise (Proof_error (line_no, "事実 " ^ argument ^ " が見つかりません"))
          | Some fact when alpha_equal fact goal.target ->
              let environment = canonical_environment goal in
              let kernel_state =
                match context_index argument goal.context with
              | Some index ->
                  verify_user_transition line_no (Verified.TacExact index)
                    state.kernel_state rest []
                    environment environment
              | None ->
                  let axiom =
                    match fixed_axiom_kind
                      (String.lowercase_ascii argument) with
                    | Some kind -> Verified.fixed_axiom kind
                    | None -> verified_error line_no
                  in
                  verify_rule_transition line_no [axiom]
                    [Verified.RAxiom] state.kernel_state rest []
                    environment environment
              in
              add_step state ("exact " ^ argument) rest kernel_state
          | Some _ -> raise (Proof_error (line_no, argument ^ " の型は現在のゴールと一致しません"))
          end
      | "apply" ->
          begin match lookup_fact argument goal.context with
          | None -> raise (Proof_error (line_no, "定理・仮定・公理 " ^ argument ^ " が見つかりません"))
          | Some fact ->
              begin match apply_fact fact goal with
              | Error message -> raise (Proof_error (line_no, message))
              | Ok (new_goals, substitutions) ->
                  let rec forall_names names = function
                    | Forall (name, body) -> forall_names (name :: names) body
                    | body -> (List.rev names, body)
                  in
                  let binders, _ = forall_names [] fact in
                  let terms =
                    List.map
                      (fun binder ->
                         Option.value (StringMap.find_opt binder substitutions)
                           ~default:binder)
                      binders
                  in
                  let environment =
                    List.fold_left add_free_name
                      (canonical_environment goal) terms
                  in
                  let term_indices =
                    List.map
                      (fun term ->
                         match list_index term 0 environment with
                         | Some index -> index
                         | None -> verified_error line_no)
                      terms
                  in
                  let original_fact_db = db_formula [] environment fact in
                  let rec specialization_plan current indices commands =
                    match indices, current with
                    | [], _ -> (current, commands)
                    | term_index :: tail, Verified.All body ->
                        specialization_plan
                          (Verified.instantiate term_index body)
                          tail
                          (Verified.RAllElim (body, term_index) :: commands)
                    | _ -> verified_error line_no
                  in
                  let _, all_commands =
                    specialization_plan original_fact_db term_indices []
                  in
                  let implication_commands =
                    List.rev new_goals
                    |> List.map (fun premise ->
                         Verified.RImplElim
                           (db_formula [] environment premise.target))
                  in
                  let close_command, axioms =
                    match context_index argument goal.context with
                    | Some index ->
                        (Verified.RHypothesis index, [])
                    | None ->
                        let axiom =
                          match fixed_axiom_kind
                            (String.lowercase_ascii argument) with
                          | Some kind -> Verified.fixed_axiom kind
                          | None -> verified_error line_no
                        in
                        (Verified.RAxiom, [axiom])
                  in
                  let commands =
                    implication_commands @ all_commands @ [close_command]
                  in
                  apply_rule_transition line_no state axioms commands
                    ("apply " ^ argument) new_goals rest
                    environment environment
              end
          end
      | "specialize" ->
          let words =
            String.split_on_char ' ' argument
            |> List.map trim
            |> List.filter (fun word -> word <> "")
          in
          let rec split_as before = function
            | ["as"; new_name] -> (List.rev before, new_name)
            | "as" :: _ ->
                raise (Proof_error (line_no,
                  "specialize H a as H_a の形で指定します"))
            | word :: rest -> split_as (word :: before) rest
            | [] ->
                raise (Proof_error (line_no,
                  "具体化した事実の名前を as の後に指定します"))
          in
          let source_and_terms, new_name = split_as [] words in
          begin match source_and_terms with
          | source :: terms when terms <> [] ->
              if List.mem_assoc new_name goal.context then
                raise (Proof_error (line_no, "同じ名前の仮定がすでにあります"));
              let fact =
                match lookup_fact source goal.context with
                | Some fact -> fact
                | None ->
                    raise (Proof_error (line_no,
                      "全称量化された事実 " ^ source ^ " が見つかりません"))
              in
              let instantiated =
                List.fold_left
                  (fun current term ->
                     match current with
                     | Forall (bound, body) -> subst bound term body
                     | _ ->
                         raise (Proof_error (line_no,
                           "指定した項の数が全称量化子の数を超えています")))
                  fact terms
              in
              let next = {
                goal with
                context = (new_name, instantiated) :: goal.context;
              } in
              let environment =
                List.fold_left add_free_name
                  (canonical_environment goal) terms
              in
              let term_indices =
                List.map
                  (fun term ->
                     match list_index term 0 environment with
                     | Some index -> index
                     | None -> verified_error line_no)
                  terms
              in
              let original_fact_db = db_formula [] environment fact in
              let rec specialization_plan current indices commands =
                match indices, current with
                | [], _ -> (current, commands)
                | term_index :: tail, Verified.All body ->
                    specialization_plan
                      (Verified.instantiate term_index body)
                      tail
                      (Verified.RAllElim (body, term_index) :: commands)
                | _ ->
                    raise (Proof_error (line_no,
                      "指定した項の数が全称量化子の数を超えています"))
              in
              let instantiated_db, all_commands =
                specialization_plan original_fact_db term_indices []
              in
              let close_command, axioms =
                match context_index source goal.context with
                | Some index ->
                    (Verified.RHypothesis index, [])
                | None ->
                    let axiom =
                      match fixed_axiom_kind
                        (String.lowercase_ascii source) with
                      | Some kind -> Verified.fixed_axiom kind
                      | None -> verified_error line_no
                    in
                    (Verified.RAxiom, [axiom])
              in
              let commands =
                Verified.RCut instantiated_db ::
                all_commands @ [close_command]
              in
              apply_rule_transition line_no state axioms commands
                ("specialize " ^ source ^ " as " ^ new_name)
                [next] rest environment environment
          | _ ->
              raise (Proof_error (line_no,
                "specialize H a as H_a の形で、具体化する項を指定します"))
          end
      | "cases" ->
          let words =
            String.split_on_char ' ' argument
            |> List.map trim
            |> List.filter (fun word -> word <> "")
          in
          begin match words with
          | fact_name :: names ->
              begin match List.assoc_opt fact_name goal.context with
              | None -> raise (Proof_error (line_no, "仮定 " ^ fact_name ^ " が見つかりません"))
              | Some (And (a, b)) ->
                  let left_name, right_name =
                    match names with
                    | [left_name; right_name] -> (left_name, right_name)
                    | [] -> (fact_name ^ "_left", fact_name ^ "_right")
                    | _ -> raise (Proof_error (line_no, "cases H [H1 H2] の形で指定します"))
                  in
                  if List.mem_assoc left_name goal.context || List.mem_assoc right_name goal.context then
                    raise (Proof_error (line_no, "分解後の仮定名は未使用の名前にします"));
                  let context = (right_name, b) :: (left_name, a) :: goal.context in
                  let next = { goal with context } in
                  let environment = canonical_environment goal in
                  apply_user_transition line_no state
                    (Verified.TacCases
                      (Option.get
                        (context_index fact_name goal.context)))
                    ("cases " ^ fact_name) [next] rest
                    environment environment
              | Some (Iff (a, b)) ->
                  let forward_name, backward_name =
                    match names with
                    | [forward_name; backward_name] -> (forward_name, backward_name)
                    | [] -> (fact_name ^ "_forward", fact_name ^ "_backward")
                    | _ -> raise (Proof_error (line_no, "cases H [H1 H2] の形で指定します"))
                  in
                  if List.mem_assoc forward_name goal.context || List.mem_assoc backward_name goal.context then
                    raise (Proof_error (line_no, "分解後の仮定名は未使用の名前にします"));
                  let context =
                    (backward_name, Imp (b, a)) ::
                    (forward_name, Imp (a, b)) :: goal.context
                  in
                  let next = { goal with context } in
                  let environment = canonical_environment goal in
                  apply_user_transition line_no state
                    (Verified.TacCases
                      (Option.get
                        (context_index fact_name goal.context)))
                    ("cases " ^ fact_name) [next] rest
                    environment environment
              | Some (Exists (bound, body)) ->
                  let witness, hypothesis =
                    match names with
                    | [witness; hypothesis] -> (witness, hypothesis)
                    | _ -> raise (Proof_error (line_no, "存在仮定には cases H witness Hw と書きます"))
                  in
                  let forbidden =
                    StringSet.union (context_free_vars goal.context) (free_vars goal.target)
                  in
                  if StringSet.mem witness forbidden then
                    raise (Proof_error (line_no, "存在除去の証人変数は文脈とゴールに現れない新しい名前にします"));
                  if List.mem_assoc hypothesis goal.context then
                    raise (Proof_error (line_no, "分解後の仮定名は未使用の名前にします"));
                  let context = (hypothesis, subst bound witness body) :: goal.context in
                  let next = { goal with context } in
                  let before_environment = canonical_environment goal in
                  let generated_environment = witness :: before_environment in
                  apply_user_transition line_no state
                    (Verified.TacCases
                      (Option.get
                        (context_index fact_name goal.context)))
                    ("cases " ^ fact_name) [next] rest
                    before_environment generated_environment
              | Some _ ->
                  raise (Proof_error (line_no, "cases は連言・同値・存在量化された仮定に使います"))
              end
          | [] -> raise (Proof_error (line_no, "分解する仮定の名前が必要です"))
          end
      | "refl" ->
          begin match goal.target with
          | Eq (a, b) when a = b ->
              let environment = canonical_environment goal in
              apply_user_transition line_no state Verified.TacRefl
                "refl" [] rest environment environment
          | _ -> raise (Proof_error (line_no, "refl は t = t の形のゴールにだけ使えます"))
          end
      | "split" | "constructor" ->
          begin match goal.target with
          | And (a, b) ->
              let generated =
                [{ goal with target = a }; { goal with target = b }]
              in
              let environment = canonical_environment goal in
              apply_user_transition line_no state Verified.TacSplit
                "split" generated rest environment environment
          | Iff (a, b) ->
              let generated =
                [{ goal with target = Imp (a, b) };
                 { goal with target = Imp (b, a) }]
              in
              let environment = canonical_environment goal in
              apply_user_transition line_no state Verified.TacSplit
                "split" generated rest environment environment
          | _ -> raise (Proof_error (line_no, "split は連言または同値のゴールに使います"))
          end
      | "left" ->
          begin match goal.target with
          | Or (a, _) ->
              let next = { goal with target = a } in
              let environment = canonical_environment goal in
              apply_user_transition line_no state Verified.TacLeft
                "left" [next] rest environment environment
          | _ -> raise (Proof_error (line_no, "left は選言のゴールに使います"))
          end
      | "right" ->
          begin match goal.target with
          | Or (_, b) ->
              let next = { goal with target = b } in
              let environment = canonical_environment goal in
              apply_user_transition line_no state Verified.TacRight
                "right" [next] rest environment environment
          | _ -> raise (Proof_error (line_no, "right は選言のゴールに使います"))
          end
      | "use" ->
          if argument = "" then raise (Proof_error (line_no, "存在証人となる変数が必要です"));
          begin match goal.target with
          | Exists (x, body) ->
              let next = { goal with target = subst x argument body } in
              let environment =
                add_free_name (canonical_environment goal) argument
              in
              let term_index =
                Option.get (list_index argument 0 environment)
              in
              apply_user_transition line_no state
                (Verified.TacUse term_index) ("use " ^ argument)
                [next] rest environment environment
          | _ -> raise (Proof_error (line_no, "use は存在量化のゴールに使います"))
          end
      | "contradiction" ->
          let has_bottom = List.exists (fun (_, f) -> alpha_equal f Bottom) goal.context in
          let has_pair =
            List.exists
              (fun (_, f) ->
                 List.exists
                   (fun (_, g) ->
                      match f, g with
                      | Not a, b | b, Not a -> alpha_equal a b
                      | _ -> false)
                   goal.context)
              goal.context
          in
          if has_bottom || has_pair then begin
            let environment = canonical_environment goal in
            apply_user_transition line_no state
              Verified.TacContradiction "contradiction"
              [] rest environment environment
          end
          else raise (Proof_error (line_no, "矛盾する仮定が見つかりません"))
      | _ -> raise (Proof_error (line_no, "未知のタクティクです: " ^ command))
      end

let find_colon s =
  match String.index_opt s ':' with
  | Some i -> i
  | None -> raise (Parse_error (0, "theorem 行には : が必要です"))

let valid_definition_name name =
  let length = String.length name in
  let reserved =
    List.mem (String.lowercase_ascii name)
      ["not"; "and"; "or"; "forall"; "exists"; "in"; "false"]
  in
  length > 0
  && not reserved
  && (match name.[0] with
      | 'a' .. 'z' | 'A' .. 'Z' | '_' -> true
      | _ -> false)
  && String.for_all is_ascii_ident_char name

let drop_optional_final_dot text =
  let text = trim text in
  let length = String.length text in
  if length > 0 && text.[length - 1] = '.' then
    trim (String.sub text 0 (length - 1))
  else text

let find_assignment text =
  let rec search index =
    if index + 2 > String.length text then None
    else if starts_with_at text index ":=" then Some index
    else search (index + 1)
  in
  search 0

let parse_definition line_no definitions line =
  let prefix = "definition " in
  let content =
    trim (String.sub line (String.length prefix)
      (String.length line - String.length prefix))
  in
  let assignment =
    match find_assignment content with
    | Some index -> index
    | None ->
        raise (Proof_error (line_no,
          "Definition 名前 引数... := 論理式 の形で書きます"))
  in
  let declaration =
    String.sub content 0 assignment
    |> trim
    |> String.split_on_char ' '
    |> List.map trim
    |> List.filter (fun word -> word <> "")
  in
  let name, parameters =
    match declaration with
    | name :: parameters -> (name, parameters)
    | [] -> raise (Proof_error (line_no, "定義名が必要です"))
  in
  if not (valid_definition_name name) then
    raise (Proof_error (line_no, "定義名が不正です: " ^ name));
  if Option.is_some (find_definition name definitions) then
    raise (Proof_error (line_no, "命題 " ^ name ^ " はすでに定義されています"));
  List.iter
    (fun parameter ->
       if not (valid_definition_name parameter) then
         raise (Proof_error (line_no,
           "定義の引数名が不正です: " ^ parameter)))
    parameters;
  let parameter_set = StringSet.of_list parameters in
  if StringSet.cardinal parameter_set <> List.length parameters then
    raise (Proof_error (line_no, "定義の引数名が重複しています"));
  let statement =
    String.sub content (assignment + 2)
      (String.length content - assignment - 2)
    |> drop_optional_final_dot
  in
  if statement = "" then
    raise (Proof_error (line_no, ":= の後に論理式が必要です"));
  let body =
    try parse_formula statement |> unfold line_no definitions
    with Parse_error (_, message) -> raise (Proof_error (line_no, message))
  in
  let undeclared = StringSet.diff (free_vars body) parameter_set in
  if not (StringSet.is_empty undeclared) then begin
    let variables = String.concat ", " (StringSet.elements undeclared) in
    raise (Proof_error (line_no,
      "定義本体に宣言されていない自由変数があります: " ^ variables))
  end else
    definitions @ [{
      definition_name = name;
      parameters;
      body;
    }]

let analyze_script script =
  let meaningful = split_statements script in
  let rec read_definitions definitions = function
    | (line_no, line) :: rest
      when starts_with_at (String.lowercase_ascii line) 0 "definition " ->
        read_definitions (parse_definition line_no definitions line) rest
    | rest -> (definitions, rest)
  in
  let definitions, proof = read_definitions [] meaningful in
  match proof with
  | [] when definitions <> [] ->
      ({
        theorem_name = "";
        theorem = Bottom;
        definitions;
        kernel_state = Verified.start Verified.Falsum;
        display_goals = [];
        steps = [];
      }, false)
  | [] -> raise (Proof_error (1, "証明スクリプトが空です"))
  | (header_line, header) :: tactics ->
      let lower_header = String.lowercase_ascii header in
      let prefix = "theorem " in
      if not (starts_with_at lower_header 0 prefix) then
        raise (Proof_error (header_line,
          "Definition 行の後は theorem 名前 : 論理式 と書きます"));
      let content = trim (String.sub header (String.length prefix) (String.length header - String.length prefix)) in
      let colon =
        try find_colon content
        with Parse_error (_, message) -> raise (Proof_error (header_line, message))
      in
      let name = trim (String.sub content 0 colon) in
      let statement = trim (String.sub content (colon + 1) (String.length content - colon - 1)) in
      if name = "" then raise (Proof_error (header_line, "定理名が必要です"));
      let theorem =
        try parse_formula statement |> unfold header_line definitions
        with Parse_error (_, message) -> raise (Proof_error (header_line, message))
      in
      let environment =
        free_vars theorem |> StringSet.elements
      in
      let initial = {
        theorem_name = name;
        theorem;
        definitions;
        kernel_state =
          Verified.start (db_formula [] environment theorem);
        display_goals = [{
          context = [];
          target = theorem;
          environment;
        }];
        steps = [];
      } in
      let rec run state = function
        | [] -> (state, false)
        | (line_no, line) :: rest when String.lowercase_ascii line = "qed" ->
            if state.display_goals <> []
               || not (Verified.solved state.kernel_state) then
              raise (Proof_error (line_no, "未解決のゴールが残っているため qed できません"));
            if rest <> [] then
              raise (Proof_error (fst (List.hd rest), "qed の後に余分な入力があります"));
            (state, true)
        | (line_no, line) :: rest ->
            run (execute_tactic line_no state line) rest
      in
      run initial tactics

let check_script script =
  let state, _ = analyze_script script in
  if state.theorem_name = "" then state
  else if state.display_goals = []
          && Verified.solved state.kernel_state then state
  else
    let line = List.length (String.split_on_char '\n' script) in
    raise (Proof_error (line, "未解決のゴールが残っています"))

let json_escape s =
  let b = Buffer.create (String.length s + 16) in
  String.iter
    (function
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | '\n' -> Buffer.add_string b "\\n"
      | '\r' -> Buffer.add_string b "\\r"
      | '\t' -> Buffer.add_string b "\\t"
      | c when Char.code c < 32 -> Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
      | c -> Buffer.add_char b c)
    s;
  Buffer.contents b

let quote s = "\"" ^ json_escape s ^ "\""

let axiom_json ax =
  Printf.sprintf {|{"key":%s,"title":%s,"statement":%s,"note":%s,"kernel":%s}|}
    (quote ax.key) (quote ax.title) (quote ax.statement) (quote ax.note)
    (if Option.is_some ax.parsed then "true" else "false")

let axioms_json () = "[" ^ String.concat "," (List.map axiom_json axioms) ^ "]"

let definition_json definition =
  let parameters =
    definition.parameters
    |> List.map quote
    |> String.concat ","
  in
  Printf.sprintf {|{"name":%s,"parameters":[%s],"statement":%s}|}
    (quote definition.definition_name)
    parameters
    (quote (formula_to_string definition.body))

let definitions_json definitions =
  "[" ^ String.concat ","
    (List.map definition_json definitions) ^ "]"

let success_json state =
  if state.theorem_name = "" then
    Printf.sprintf
      {|{"ok":true,"definitionsOnly":true,"definitions":%s,"steps":0,"message":%s}|}
      (definitions_json state.definitions)
      (quote "命題定義を読み込みました")
  else
    Printf.sprintf
      {|{"ok":true,"definitionsOnly":false,"theorem":%s,"statement":%s,"definitions":%s,"steps":%d,"message":%s}|}
      (quote state.theorem_name)
      (quote (formula_to_string state.theorem))
      (definitions_json state.definitions)
      (List.length state.steps)
      (quote "証明がカーネルによって検証されました")

let context_entry_json (name, formula) =
  Printf.sprintf {|{"name":%s,"formula":%s}|}
    (quote name) (quote (formula_to_string formula))

let goal_json goal =
  let context =
    List.rev goal.context
    |> List.map context_entry_json
    |> String.concat ","
  in
  Printf.sprintf {|{"target":%s,"context":[%s]}|}
    (quote (formula_to_string goal.target)) context

let step_json state has_qed =
  if state.theorem_name = "" then
    Printf.sprintf
      {|{"ok":true,"definitionsOnly":true,"definitions":%s,"steps":0,"complete":true,"qed":false,"goals":[],"message":%s}|}
      (definitions_json state.definitions)
      (quote "命題定義を読み込みました。続けて theorem を書けます")
  else
    let complete = Verified.solved state.kernel_state in
    let goals =
      List.map goal_json state.display_goals |> String.concat ","
    in
    let message =
      if has_qed then "証明が完了し、カーネルによって検証されました"
      else if complete then "すべてのゴールが解決しました。qed で証明を完了できます"
      else "現在のゴールに次のタクティクを入力してください"
    in
    Printf.sprintf
      {|{"ok":true,"definitionsOnly":false,"theorem":%s,"statement":%s,"definitions":%s,"steps":%d,"complete":%s,"qed":%s,"goals":[%s],"message":%s}|}
      (quote state.theorem_name)
      (quote (formula_to_string state.theorem))
      (definitions_json state.definitions)
      (List.length state.steps)
      (if complete then "true" else "false")
      (if has_qed then "true" else "false")
      goals
      (quote message)

let error_json line message =
  Printf.sprintf {|{"ok":false,"line":%d,"message":%s}|} line (quote message)

let read_file path =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () ->
       let length = in_channel_length ic in
       really_input_string ic length)

let mime_type path =
  if Filename.check_suffix path ".html" then "text/html; charset=utf-8"
  else if Filename.check_suffix path ".css" then "text/css; charset=utf-8"
  else if Filename.check_suffix path ".js" then "application/javascript; charset=utf-8"
  else "application/octet-stream"

let send_response oc status content_type body =
  Printf.fprintf oc "HTTP/1.1 %s\r\n" status;
  Printf.fprintf oc "Content-Type: %s\r\n" content_type;
  Printf.fprintf oc "Content-Length: %d\r\n" (String.length body);
  Printf.fprintf oc "Cache-Control: no-store\r\n";
  Printf.fprintf oc "Connection: close\r\n\r\n";
  output_string oc body;
  flush oc

let rec read_headers ic content_length =
  match input_line ic with
  | exception End_of_file -> content_length
  | line ->
      let line = trim line in
      if line = "" then content_length
      else
        let lower = String.lowercase_ascii line in
        let prefix = "content-length:" in
        let length =
          if starts_with_at lower 0 prefix then
            try int_of_string (trim (String.sub line (String.length prefix) (String.length line - String.length prefix)))
            with Failure _ -> 0
          else content_length
        in
        read_headers ic length

let web_root = ref "web"

let handle_client socket =
  let ic = Unix.in_channel_of_descr socket in
  let oc = Unix.out_channel_of_descr socket in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic; close_out_noerr oc)
    (fun () ->
       match input_line ic with
       | exception End_of_file -> ()
       | request ->
           let parts = String.split_on_char ' ' (trim request) in
           let method_, path =
             match parts with
             | method_ :: path :: _ -> (method_, path)
             | _ -> ("", "")
           in
           let content_length = read_headers ic 0 in
           let body = if content_length > 0 then really_input_string ic content_length else "" in
           match method_, path with
           | "GET", "/api/health" ->
               send_response oc "200 OK" "application/json; charset=utf-8"
                 {|{"ok":true,"service":"zfcert","kernel":"coq-extracted"}|}
           | "GET", "/api/axioms" ->
               send_response oc "200 OK" "application/json; charset=utf-8" (axioms_json ())
           | "POST", "/api/check" ->
               let response =
                 try
                   let state = check_script body in
                   success_json state
                 with
                 | Proof_error (line, message) -> error_json line message
                 | Parse_error (_, message) -> error_json 1 message
                 | exn -> error_json 1 ("内部エラー: " ^ Printexc.to_string exn)
               in
               send_response oc "200 OK" "application/json; charset=utf-8" response
           | "POST", "/api/step" ->
               let response =
                 try
                   let state, has_qed = analyze_script body in
                   step_json state has_qed
                 with
                 | Proof_error (line, message) -> error_json line message
                 | Parse_error (_, message) -> error_json 1 message
                 | exn -> error_json 1 ("内部エラー: " ^ Printexc.to_string exn)
               in
               send_response oc "200 OK" "application/json; charset=utf-8" response
           | "GET", ("/" | "/index.html") ->
               let path = Filename.concat !web_root "index.html" in
               begin try send_response oc "200 OK" (mime_type path) (read_file path)
               with Sys_error _ -> send_response oc "404 Not Found" "text/plain" "index.html not found"
               end
           | "GET", ("/style.css" | "/app.js" as resource) ->
               let path = Filename.concat !web_root (String.sub resource 1 (String.length resource - 1)) in
               begin try send_response oc "200 OK" (mime_type path) (read_file path)
               with Sys_error _ -> send_response oc "404 Not Found" "text/plain" "not found"
               end
           | _ -> send_response oc "404 Not Found" "application/json" {|{"error":"not found"}|})

let serve port =
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  let socket = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  Unix.setsockopt socket Unix.SO_REUSEADDR true;
  Unix.bind socket (Unix.ADDR_INET (Unix.inet_addr_loopback, port));
  Unix.listen socket 32;
  Printf.printf "ZFCert: http://127.0.0.1:%d\n%!" port;
  while true do
    let client, _ = Unix.accept socket in
    try handle_client client
    with exn ->
      prerr_endline ("request failed: " ^ Printexc.to_string exn);
      Unix.close client
  done

let run_self_tests () =
  let terminate_lines script =
    script
    |> String.split_on_char '\n'
    |> List.map (fun line ->
         if trim line = "" then line else line ^ ".")
    |> String.concat "\n"
  in
  let valid = [
    "theorem refl : forall x, x = x\nintro x\nrefl\nqed";
    "theorem empty : exists e, forall x, not (x in e)\nexact empty_set\nqed";
    "theorem ext : forall a, forall b, ((forall z, (z in a <-> z in b)) -> a = b)\nintro a\nintro b\nintro H\napply extensionality\nexact H\nqed";
    "theorem ext_specialized : forall a, forall b, ((forall z, (z in a <-> z in b)) -> a = b)\nintro a\nintro b\nintro H\nspecialize extensionality a b as E\napply E\nexact H\nqed";
    "theorem sep : forall a, exists b, forall x, (x in b <-> (x in a and not (x in x)))\nintro a\nseparation S a x : not (x in x)\nexact S\nqed";
    "theorem rep : forall a, ((forall x, exists y, (y = x and forall z, (z = x -> z = y))) -> exists b, forall y, (y in b <-> exists x, (x in a and y = x)))\nintro a\nreplacement R a x y : y = x\nexact R\nqed";
    "theorem universal_contradiction : forall a, forall b, ((forall x, not (x in b)) -> (a in b -> b in a))\nintro a\nintro b\nintro H\nintro Ha\nspecialize H a as Hna\ncontradiction\nqed";
    "Definition is_empty x := forall y, not (y in x)\nDefinition empty_alias x := is_empty x\ntheorem definition_identity : forall a, (empty_alias a -> is_empty a)\nintro a\nintro H\nexact H\nqed";
    "Definition has_equal x := exists y, y = x\ntheorem definition_avoids_capture : forall y, (has_equal y -> exists z, z = y)\nintro y\nintro H\nexact H\nqed";
    "Definition relates x y := x = y\ntheorem simultaneous_arguments : forall x, forall y, (relates y x -> y = x)\nintro x\nintro y\nintro H\nexact H\nqed";
    "theorem rule_identity : forall x, x = x\nrule all_intro x\nrule equal_refl\nqed";
    "theorem rule_cut : forall x, x = x\nrule cut H : forall x, x = x\nrule all_intro x\nrule equal_refl\nrule hypothesis H\nqed";
    "theorem rule_equal_elim : forall s, forall t, (s = t -> (s in s -> s in t))\nrule all_intro s\nrule all_intro t\nrule impl_intro Heq\nrule impl_intro Hmem\nrule equal_elim s t x : s in x\nrule hypothesis Heq\nrule hypothesis Hmem\nqed";
    "theorem rule_all_elim : forall a, ((forall x, x = x) -> a = a)\nrule all_intro a\nrule impl_intro H\nrule all_elim a x : x = x\nrule hypothesis H\nqed";
    "theorem rule_axiom : exists e, forall x, not (x in e)\nrule axiom\nqed";
    "theorem rule_impl_elim : forall a, forall b, ((a = a -> b = b) -> (a = a -> b = b))\nrule all_intro a\nrule all_intro b\nrule impl_intro Himp\nrule impl_intro Ha\nrule impl_elim : a = a\nrule hypothesis Himp\nrule hypothesis Ha\nqed";
    "theorem rule_conjunction : forall a, forall b, ((a = a and b = b) -> (b = b and a = a))\nrule all_intro a\nrule all_intro b\nrule impl_intro H\nrule conj_intro\nrule conj_elim_r : a = a\nrule hypothesis H\nrule conj_elim_l : b = b\nrule hypothesis H\nqed";
    "theorem rule_disjunction : forall a, forall b, ((a = a or b = b) -> (a = a or b = b))\nrule all_intro a\nrule all_intro b\nrule impl_intro H\nrule disj_elim HA HB : a = a ; b = b\nrule hypothesis H\nrule disj_intro_l\nrule hypothesis HA\nrule disj_intro_r\nrule hypothesis HB\nqed";
    "theorem rule_ex_elim : (exists x, x = x) -> exists y, y = y\nrule impl_intro H\nrule ex_elim x Hx : x = x\nrule hypothesis H\nrule ex_intro x\nrule equal_refl\nqed";
    "theorem rule_falsum : forall a, (false -> a = a)\nrule all_intro a\nrule impl_intro H\nrule falsum_elim\nrule hypothesis H\nqed";
    "theorem rule_separation_axiom : forall a, exists b, forall x, (x in b <-> (x in a and not (x in x)))\nrule all_intro a\nrule axiom separation a x : not (x in x)\nqed";
    "theorem rule_replacement_axiom : forall a, ((forall x, exists y, (y = x and forall z, (z = x -> z = y))) -> exists b, forall y, (y in b <-> exists x, (x in a and y = x)))\nrule all_intro a\nrule axiom replacement a x y : y = x\nqed";
  ] in
  List.iter
    (fun script ->
       let state = check_script (terminate_lines script) in
       let printed = formula_to_string state.theorem in
       if not (alpha_equal state.theorem (parse_formula printed)) then
         failwith ("pretty-printed theorem did not round-trip: " ^ printed))
    valid;
  let interactive, has_qed =
    analyze_script
      (terminate_lines
        "theorem interactive : forall x, x = x\nintro x")
  in
  if has_qed || List.length interactive.display_goals <> 1 then
    failwith "interactive analysis did not preserve the current goal";
  let invalid =
    "theorem bad : forall x, forall y, x = y\nintro x\nintro y\nrefl\nqed"
  in
  let rejected =
    try ignore (check_script (terminate_lines invalid)); false
    with Proof_error _ -> true
  in
  if not rejected then failwith "kernel accepted an invalid equality proof";
  let definition_as_fact_rejected =
    try
      ignore (check_script (terminate_lines
        "Definition foo := forall x, x = x\ntheorem bad_definition_fact : foo\nexact foo\nqed"));
      false
    with Proof_error _ -> true
  in
  if not definition_as_fact_rejected then
    failwith "a proposition definition was incorrectly accepted as a proof";
  let missing_period_rejected =
    try
      ignore (analyze_script "theorem missing_period : forall x, x = x");
      false
    with Proof_error _ -> true
  in
  if not missing_period_rejected then
    failwith "a statement without a final period was accepted";
  let old_quantifier_syntax_rejected =
    try
      ignore (analyze_script
        "theorem old_quantifier : forall x. x = x.
         rule all_intro x.
         rule equal_refl.
         qed.");
      false
    with Proof_error _ -> true
  in
  if not old_quantifier_syntax_rejected then
    failwith "the old quantifier period syntax was accepted";
  ignore (check_script
    "theorem multiline :
       forall x,
         x = x.
     rule
       all_intro x.
     rule equal_refl.
     qed.");
  begin match find_axiom "choice" with
  | Some { parsed = Some _; _ } -> ()
  | _ -> failwith "choice axiom did not parse"
  end;
  Printf.printf "All %d kernel tests passed (plus 4 rejection tests).\n%!" (List.length valid)

let () =
  let port = ref 8080 in
  let self_test = ref false in
  let specs = [
    ("--port", Arg.Set_int port, "listen port (default: 8080)");
    ("--web-root", Arg.Set_string web_root, "directory containing web assets");
    ("--self-test", Arg.Set self_test, "run kernel tests and exit");
  ] in
  Arg.parse specs (fun _ -> ()) "zfcert [--port PORT]";
  if !self_test then run_self_tests () else serve !port
