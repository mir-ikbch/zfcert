(* ZFCert proof-language evaluation and interactive session state. *)

open Syntax

module StringMap = Map.Make (String)
module StringSet = Syntax.StringSet

(** The extracted state is the authoritative logical state.  Its type is
    abstract, so this module can only create and advance it through the
    extracted kernel API. *)
module Extracted = Zfcert_kernel
module Kernel_syntax = Kernel_syntax

exception Parse_error = Parser.Parse_error

let parse_formula = Parser.parse_formula

let is_ascii_ident_char = function
  | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' -> true
  | _ -> false

let starts_with_at input index prefix =
  let length = String.length prefix in
  index + length <= String.length input
  && String.sub input index length = prefix

type axiom = {
  key : string;
  title : string;
  statement : string;
  note : string;
  parsed : formula option;
}

let axiom_data =
  [
    ("empty_set", "Empty set",
     "exists e, forall x, not (x in e)",
     "There is a set with no elements.");
    ("extensionality", "Extensionality",
     "forall x, forall y, ((forall z, (z in x <-> z in y)) -> x = y)",
     "Sets with the same elements are equal.");
    ("pairing", "Pairing",
     "forall a, forall b, exists p, forall x, (x in p <-> (x = a or x = b))",
     "Every two sets have a pair set.");
    ("union", "Union",
     "forall a, exists u, forall x, (x in u <-> exists y, (x in y and y in a))",
     "Every set has a union.");
    ("power_set", "Power set",
     "forall a, exists p, forall x, (x in p <-> forall z, (z in x -> z in a))",
     "Every set has a power set.");
    ("infinity", "Infinity",
     "exists i, ((exists e, ((forall z, not (z in e)) and e in i)) and forall x, (x in i -> exists s, (s in i and forall z, (z in s <-> (z in x or z = x)))))",
     "An inductive set exists.");
    ("foundation", "Foundation",
     "forall x, ((exists a, a in x) -> exists y, (y in x and forall z, (z in y -> not (z in x))))",
     "Every nonempty set has an element disjoint from it.");
    ("separation", "Separation schema",
     "forall a, exists b, forall x, (x in b <-> (x in a and P))",
     "P may be any formula; this entry displays the schema template.");
    ("replacement", "Replacement schema",
     "FUNCTIONAL(P) -> forall a, exists b, forall y, (y in b <-> exists x, (x in a and P))",
     "The schema instance for each formula P that defines a function.");
    ("choice", "Choice",
     "forall a, ((forall x, (x in a -> exists y, y in x)) -> exists c, forall x, (x in a -> exists y, ((y in x and y in c) and forall z, ((z in x and z in c) -> z = y))))",
     "A choice set exists for every family of nonempty sets.");
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

type goal = {
  variables : string list;
  context : (string * formula) list;
  target : formula;
}

type proposition_alias = {
  alias_name : string;
  parameters : string list;
  body : formula;
}

type term_definition = {
  definition_name : string;
  parameters : string list;
  body : term;
}

(** A [choose] declaration extends the extracted global environment.  With
    specialization terms it selects an existential witness; without terms it
    introduces a certified Skolem function for a universal-existential fact. *)
type choose_declaration = {
  choose_line : int;
  choose_name : string;
  choose_fact : string;
  choose_source : string;
  choose_terms : string list;
}

type session = {
  theorem_name : string;
  theorem : formula;
  aliases : proposition_alias list;
  definitions : term_definition list;
  global_environment : Extracted.environment;
  hidden_global_facts : StringSet.t;
  put_facts : StringSet.t;
  kernel_state : Extracted.state;
  final_certificate : Extracted.certificate option;
  (* Reverse chronological bookkeeping; public step_count is order-independent. *)
  steps : string list;
}

exception Proof_error of int * string

let trim = String.trim

let find_alias name aliases =
  List.find_opt
    (fun alias -> alias.alias_name = name)
    aliases

let find_definition name definitions =
  List.find_opt (fun definition -> definition.definition_name = name) definitions

(* Substitute simultaneously: an argument is never substituted a second time. *)
let rec substitute_term substitutions = function
  | Name name as term ->
      Option.value (StringMap.find_opt name substitutions) ~default:term
  | App (name, arguments) ->
      App (name, List.map (substitute_term substitutions) arguments)

let check_definition_arity line_no definition arguments =
  let expected = List.length definition.parameters in
  let actual = List.length arguments in
  if expected <> actual then
    raise (Proof_error (line_no,
      Printf.sprintf
        "Definition %s expects %d arguments, but received %d."
        definition.definition_name expected actual))

let rec unfold_term line_no definitions bound term =
  let expand name arguments fallback =
    match find_definition name definitions with
    | None -> fallback
    | Some definition ->
        check_definition_arity line_no definition arguments;
        let substitutions =
          List.fold_left2
            (fun substitutions parameter argument ->
               StringMap.add parameter argument substitutions)
            StringMap.empty definition.parameters arguments
        in
        (* Bodies were expanded when declared. Do not reinterpret names inside
           substituted arguments in the scope of the definition. *)
        substitute_term substitutions definition.body
  in
  match term with
  | Name name when StringSet.mem name bound -> term
  | Name name -> expand name [] term
  | App (name, arguments) ->
      let arguments = List.map (unfold_term line_no definitions bound) arguments in
      expand name arguments (App (name, arguments))

let substitution_variables substitutions =
  StringMap.fold
    (fun variable term variables ->
       StringSet.add variable (StringSet.union (term_free_vars term) variables))
    substitutions
    StringSet.empty

let substitute_surface_term substitutions term =
  let rec go = function
    | Name name ->
        Name (Option.value (StringMap.find_opt name substitutions) ~default:name)
    | App (name, arguments) -> App (name, List.map go arguments)
  in
  go term

let rec subst_many reserved substitutions = function
  | Bottom -> Bottom
  | Named (name, arguments) ->
      Named (name, List.map (substitute_term substitutions) arguments)
  | Eq (a, b) ->
      Eq (substitute_term substitutions a,
          substitute_term substitutions b)
  | Mem (a, b) ->
      Mem (substitute_term substitutions a,
           substitute_term substitutions b)
  | Not f -> Not (subst_many reserved substitutions f)
  | And (a, b) -> And (subst_many reserved substitutions a, subst_many reserved substitutions b)
  | Or (a, b) -> Or (subst_many reserved substitutions a, subst_many reserved substitutions b)
  | Imp (a, b) -> Imp (subst_many reserved substitutions a, subst_many reserved substitutions b)
  | Iff (a, b) -> Iff (subst_many reserved substitutions a, subst_many reserved substitutions b)
  | Forall (x, f) ->
      let substitutions = StringMap.remove x substitutions in
      let captures =
        StringMap.exists
          (fun parameter argument ->
             StringSet.mem x (term_free_vars argument)
             && StringSet.mem parameter (free_vars f))
          substitutions
      in
      if captures then
        let used =
          StringSet.union reserved
            (StringSet.union (all_vars f) (substitution_variables substitutions))
        in
        let fresh = fresh_name x used in
        Forall (fresh,
          subst_many reserved substitutions (rename_bound x fresh f))
      else
        Forall (x, subst_many reserved substitutions f)
  | Exists (x, f) ->
      let substitutions = StringMap.remove x substitutions in
      let captures =
        StringMap.exists
          (fun parameter argument ->
             StringSet.mem x (term_free_vars argument)
             && StringSet.mem parameter (free_vars f))
          substitutions
      in
      if captures then
        let used =
          StringSet.union reserved
            (StringSet.union (all_vars f) (substitution_variables substitutions))
        in
        let fresh = fresh_name x used in
        Exists (fresh,
          subst_many reserved substitutions (rename_bound x fresh f))
      else
        Exists (x, subst_many reserved substitutions f)

(* Validate source arguments before expansion, including parameters that an
   alias or term definition discards. *)
let rec check_alias_argument line_no definitions constants bound = function
  | Name name when StringSet.mem name bound -> ()
  | Name name ->
      begin match find_definition name definitions with
      | Some definition -> check_definition_arity line_no definition []
      | None when StringSet.mem name constants -> ()
      | None -> raise (Proof_error (line_no,
          "Undeclared free variables in alias argument: " ^ name))
      end
  | App (name, arguments) ->
      begin match find_definition name definitions with
      | Some definition -> check_definition_arity line_no definition arguments
      | None when StringSet.mem name constants -> ()
      | None -> raise (Proof_error (line_no,
          "Undefined function name in alias argument: " ^ name))
      end;
      List.iter (check_alias_argument line_no definitions constants bound) arguments

let rec unfold_formula line_no aliases definitions constants bound = function
  | Named (name, arguments) ->
      begin match find_alias name aliases with
      | Some alias ->
          let expected = List.length alias.parameters in
          let actual = List.length arguments in
          if expected <> actual then
            raise (Proof_error (line_no,
              Printf.sprintf
                "Alias %s expects %d arguments, but received %d."
                name expected actual));
          List.iter (check_alias_argument line_no definitions constants bound) arguments;
          let arguments = List.map (unfold_term line_no definitions bound) arguments in
          let substitutions =
            List.fold_left2
              (fun substitutions parameter argument ->
                 StringMap.add parameter argument substitutions)
              StringMap.empty alias.parameters arguments
          in
          (* Bodies were expanded when declared. Expand arguments in the
             caller's scope, then substitute without reinterpreting their names
             under the alias body's binders. *)
          subst_many constants substitutions alias.body
      | None ->
          raise (Proof_error (line_no,
            "Undefined proposition name: " ^ name))
      end
  | Bottom -> Bottom
  | Eq (a, b) ->
      Eq (unfold_term line_no definitions bound a,
          unfold_term line_no definitions bound b)
  | Mem (a, b) ->
      Mem (unfold_term line_no definitions bound a,
           unfold_term line_no definitions bound b)
  | Not f -> Not (unfold_formula line_no aliases definitions constants bound f)
  | And (a, b) ->
      And (unfold_formula line_no aliases definitions constants bound a,
           unfold_formula line_no aliases definitions constants bound b)
  | Or (a, b) ->
      Or (unfold_formula line_no aliases definitions constants bound a,
          unfold_formula line_no aliases definitions constants bound b)
  | Imp (a, b) ->
      Imp (unfold_formula line_no aliases definitions constants bound a,
           unfold_formula line_no aliases definitions constants bound b)
  | Iff (a, b) ->
      Iff (unfold_formula line_no aliases definitions constants bound a,
           unfold_formula line_no aliases definitions constants bound b)
  | Forall (x, f) ->
      Forall (x, unfold_formula line_no aliases definitions constants
        (StringSet.add x bound) f)
  | Exists (x, f) ->
      Exists (x, unfold_formula line_no aliases definitions constants
        (StringSet.add x bound) f)

let unfold ?(bound = StringSet.empty) line_no aliases definitions environment formula =
  let constants = StringSet.of_list (Extracted.environment_constants environment) in
  unfold_formula line_no aliases definitions constants bound formula

let split_first_word line =
  let is_space = function
    | ' ' | '\t' | '\r' | '\n' -> true
    | _ -> false
  in
  let rec find index =
    if index >= String.length line then None
    else if is_space line.[index] then Some index
    else find (index + 1)
  in
  match find 0 with
  | None -> (line, "")
  | Some i -> (String.sub line 0 i, trim (String.sub line (i + 1) (String.length line - i - 1)))

let words text =
  let is_space = function
    | ' ' | '\t' | '\r' | '\n' -> true
    | _ -> false
  in
  let length = String.length text in
  let rec skip index =
    if index < length && is_space text.[index] then skip (index + 1)
    else index
  in
  let rec word_end index =
    if index < length && not (is_space text.[index]) then word_end (index + 1)
    else index
  in
  let rec collect index result =
    let start = skip index in
    if start >= length then List.rev result
    else
      let finish = word_end start in
      collect finish (String.sub text start (finish - start) :: result)
  in
  collect 0 []

let split_schema_argument line_no aliases definitions environment bound argument =
  match String.index_opt argument ':' with
  | None ->
      raise (Proof_error (line_no,
        "A schema instance requires : followed by a formula."))
  | Some i ->
      let names =
        String.sub argument 0 i
        |> trim
        |> words
      in
      let statement = trim (String.sub argument (i + 1) (String.length argument - i - 1)) in
      if statement = "" then
        raise (Proof_error (line_no, "Expected a formula after :."));
      let predicate =
        let variables = match names with [] -> [] | _fact :: variables -> variables in
        try parse_formula statement |> unfold
          ~bound:(List.fold_right StringSet.add variables bound)
          line_no aliases definitions environment
        with Parse_error (_, message) -> raise (Proof_error (line_no, message))
      in
      (names, predicate)

let context_free_vars context =
  List.fold_left (fun acc (_, f) -> StringSet.union acc (free_vars f)) StringSet.empty context

let kernel_formula formula =
  Kernel_syntax.to_kernel formula

let materialize_goals line state =
  let visible_hypothesis name =
    not (StringSet.mem name state.hidden_global_facts)
    || StringSet.mem name state.put_facts
  in
  match Extracted.goals ~visible_hypothesis state.kernel_state with
  | Error error ->
      raise (Proof_error (line,
        "Could not read the extracted proof state: "
        ^ (match error with
           | Extracted.MetadataMismatch -> "name metadata are inconsistent"
           | _ -> "the named kernel rejected its own goal state")))
  | Ok goals ->
      List.map
        (fun (kernel_goal : Extracted.goal_view) ->
           let context =
             kernel_goal.assumptions
             |> List.map
                 (fun (name, formula) ->
                    (name, Kernel_syntax.of_kernel formula))
           in
           let target =
             Kernel_syntax.of_kernel kernel_goal.conclusion
           in
           {
             variables = List.rev kernel_goal.variables;
             context;
             target;
           })
        goals

let kernel_error = function
  | Extracted.NoGoals -> "the proof state has no goals"
  | Extracted.HypothesisNotFound None -> "a hypothesis was not found"
  | Extracted.HypothesisNotFound (Some name) ->
      "hypothesis " ^ name ^ " was not found"
  | Extracted.HypothesisAlreadyUsed name ->
      "hypothesis " ^ name ^ " is already in use"
  | Extracted.VariableAlreadyUsed name ->
      "variable " ^ name ^ " is already in use"
  | Extracted.UnknownVariable name ->
      "variable " ^ name ^ " is unknown"
  | Extracted.FormulaMismatch -> "a formula did not match"
  | Extracted.WrongGoalShape -> "the goal has the wrong logical form"
  | Extracted.MetadataMismatch ->
      "the extracted name metadata are inconsistent"

let accept_kernel_result line operation = function
  | Ok state -> state
  | Error error ->
      raise (Proof_error (line,
        "The extracted kernel rejected the " ^ operation ^ ": "
        ^ kernel_error error ^ "."))

let verified_error line =
  raise (Proof_error (line, "Internal named-kernel invariant failed."))

let kernel_rule_run line axioms rules state =
  Extracted.rule_run ~axioms rules state
  |> accept_kernel_result line "rule"

let kernel_certificate_run line steps state =
  Extracted.run_certificate steps state
  |> accept_kernel_result line "rule program"

let lookup_fact name context =
  match List.assoc_opt name context with
  | Some f -> Some f
  | None ->
      begin match find_axiom name with
      | Some { parsed = Some f; _ } -> Some f
      | _ -> None
      end

(* Global facts are present in the extracted proof state, but facts declared
   by an earlier theorem (and facts introduced by [choose]) are deliberately
   hidden from the surface context and from automatic resolution.  Explicit
   name-based tactics may still refer to them. *)
let lookup_assumption state context name =
  match List.assoc_opt name context with
  | Some formula -> Some formula
  | None ->
      Extracted.environment_facts state.global_environment
      |> List.assoc_opt name
      |> Option.map Kernel_syntax.of_kernel

let lookup_fact_in_state state context name =
  match lookup_assumption state context name with
  | Some formula -> Some formula
  | None ->
      begin match find_axiom name with
      | Some { parsed = Some formula; _ } -> Some formula
      | _ -> None
      end

let rec instantiate_formula substitutions = function
  | Bottom -> Bottom
  | Named (name, arguments) ->
      Named (name, List.map (substitute_surface_term substitutions) arguments)
  | Eq (a, b) ->
      Eq (substitute_surface_term substitutions a,
          substitute_surface_term substitutions b)
  | Mem (a, b) ->
      Mem (substitute_surface_term substitutions a,
           substitute_surface_term substitutions b)
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
  let rec term active_metas sub p a =
    match p, a with
    | Name p, Name a when StringSet.mem p active_metas ->
        begin match StringMap.find_opt p sub with
        | None -> Some (StringMap.add p a sub)
        | Some old when old = a -> Some sub
        | Some _ -> None
        end
    | Name p, Name a when p = a -> Some sub
    | App (p_name, p_args), App (a_name, a_args)
      when p_name = a_name && List.length p_args = List.length a_args ->
        List.fold_left2
          (fun result p_arg a_arg -> Option.bind result (fun sub' -> term active_metas sub' p_arg a_arg))
          (Some sub) p_args a_args
    | _ -> None
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
        let p' = if x = y then p else subst x (Name y) p in
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

let unresolved_instantiations metas substitutions =
  StringSet.elements metas
  |> List.filter (fun name -> not (StringMap.mem name substitutions))

let cannot_infer_instantiations names =
  "Cannot infer an instantiation for universally quantified variable(s): "
  ^ String.concat ", " names
  ^ ". Use specialize first or provide a more specific goal."

let decompose_imp formula =
  let rec loop premises = function
    | Imp (a, b) -> loop (a :: premises) b
    | Not a -> (List.rev (a :: premises), Bottom)
    | f -> (List.rev premises, f)
  in
  loop [] formula

let decompose_apply_fact direction fact =
  let metas, body = decompose_forall fact in
  match direction, body with
  | None, _ ->
      let premises, conclusion = decompose_imp body in
      Ok (metas, premises, conclusion)
  (* Preserve each side as a whole, including implications and negations. *)
  | Some `Forward, Iff (left, right) -> Ok (metas, [left], right)
  | Some `Backward, Iff (left, right) -> Ok (metas, [right], left)
  | Some _, _ -> Error "Directional apply requires an equivalence (<->)."

let apply_fact (metas, premises, conclusion) goal =
  match match_formula metas conclusion goal.target with
  | None -> Error "The conclusion of this fact does not match the current goal."
  | Some sub ->
      begin match unresolved_instantiations metas sub with
      | name :: rest ->
          Error (cannot_infer_instantiations (name :: rest))
      | [] ->
          let premises = List.map (instantiate_formula sub) premises in
          Ok (premises, sub)
      end

let add_step state text kernel_state =
  { state with
    kernel_state;
    final_certificate = None;
    steps = text :: state.steps;
  }

let apply_rule_transition line_no state axioms rules text =
  let kernel_state =
    kernel_rule_run line_no axioms rules state.kernel_state
  in
  add_step state text kernel_state

let apply_primitive_rules line_no state rules text =
  apply_rule_transition line_no state [] rules text

let checked_step ?(axioms = []) rule =
  Extracted.certificate_step ~axioms rule

let apply_certificate_program line_no state program text =
  let kernel_state =
    kernel_certificate_run line_no program state.kernel_state
  in
  add_step state text kernel_state

let parse_formula_at ?(bound = StringSet.empty) line_no aliases definitions environment text =
  try parse_formula (trim text) |> unfold ~bound line_no aliases definitions environment
  with Parse_error (_, message) -> raise (Proof_error (line_no, message))

let parse_surface_term ?(bound = StringSet.empty) line_no definitions text =
  try Parser.parse_term (trim text) |> unfold_term line_no definitions bound
  with Parse_error (_, message) -> raise (Proof_error (line_no, message))

let valid_term_name name =
  name <> "" && String.for_all is_ascii_ident_char name

let last_space_index text =
  let rec find index =
    if index < 0 then None
    else
      match text.[index] with
      | ' ' | '\t' -> Some index
      | _ -> find (index - 1)
  in
  find (String.length text - 1)

let parse_separation_argument line_no aliases definitions environment bound argument =
  match String.index_opt argument ':' with
  | None ->
      raise (Proof_error (line_no,
        "A separation instance requires : followed by a formula."))
  | Some i ->
      let head = trim (String.sub argument 0 i) in
      let statement = trim (String.sub argument (i + 1) (String.length argument - i - 1)) in
      if statement = "" then
        raise (Proof_error (line_no, "Expected a formula after :."));
      let fact_name, rest = split_first_word head in
      if fact_name = "" || rest = "" then
        raise (Proof_error (line_no,
          "Use: separation S source_term x : P."));
      let source_text, element =
        match last_space_index rest with
        | None ->
            raise (Proof_error (line_no,
              "Use: separation S source_term x : P."))
        | Some split ->
            (trim (String.sub rest 0 split),
             trim (String.sub rest (split + 1) (String.length rest - split - 1)))
      in
      if source_text = "" || not (valid_term_name element) then
        raise (Proof_error (line_no,
          "Use: separation S source_term x : P."));
      let source = parse_surface_term ~bound line_no definitions source_text in
      if StringSet.mem element (term_free_vars source) then
        raise (Proof_error (line_no,
          "The element variable must not occur in the source term."));
      let predicate =
        try parse_formula statement |> unfold ~bound:(StringSet.add element bound)
          line_no aliases definitions environment
        with Parse_error (_, message) -> raise (Proof_error (line_no, message))
      in
      (fact_name, source, element, predicate)

let fixed_axiom_kind = function
  | "empty_set" -> Some Extracted.EmptySet
  | "extensionality" -> Some Extracted.Extensionality
  | "pairing" -> Some Extracted.Pairing
  | "union" -> Some Extracted.Union
  | "power_set" -> Some Extracted.PowerSet
  | "foundation" -> Some Extracted.Foundation
  | "infinity" -> Some Extracted.Infinity
  | "choice" -> Some Extracted.Choice
  | _ -> None

let execute_rule line_no state argument =
  let bound =
    match materialize_goals line_no state with
    | goal :: _ -> StringSet.of_list goal.variables
    | [] -> StringSet.empty
  in
  let parse_formula text =
    parse_formula_at ~bound line_no state.aliases state.definitions state.global_environment text
  in
  let request =
    try Rule_parser.parse ~parse_formula argument with
    | Rule_parser.Error message ->
        raise (Proof_error (line_no, message))
  in
  begin match request with
  | Extracted.NPrimitiveRule (Extracted.NRHypothesis name) ->
      begin match materialize_goals line_no state with
      | goal :: _ when Option.is_some (lookup_assumption state goal.context name) -> ()
      | _ ->
          raise (Proof_error (line_no,
            "Hypothesis not found in the current context: " ^ name))
      end
  | _ -> ()
  end;
  let kernel_state =
    Extracted.execute_rule request state.kernel_state
    |> accept_kernel_result line_no "rule"
  in
  add_step state (Rule_parser.description argument) kernel_state

let specialize_rules ?(bound = StringSet.empty) line_no definitions fact terms =
  let rec build current remaining rules =
    match remaining, current with
    | [], _ -> (current, rules)
    | term :: rest, Forall (binder, body) ->
        let surface_term = parse_surface_term ~bound line_no definitions term in
        let rule =
          Extracted.NRAllElim
            (Kernel_syntax.to_kernel_term surface_term,
             kernel_formula current)
        in
        build (subst binder surface_term body) rest (rule :: rules)
    | _ ->
        raise (Proof_error (line_no,
          "Too many terms were supplied for universal specialization."))
  in
  build fact terms []

let apply_fact_rules ~bound line_no definitions direction fact substitutions =
  let rec forall_names = function
    | Forall (name, body) -> name :: forall_names body
    | _ -> []
  in
  let terms =
    List.map (fun binder -> StringMap.find binder substitutions)
      (forall_names fact)
  in
  let instantiated, all_commands =
    specialize_rules ~bound line_no definitions fact terms
  in
  let projection =
    match direction, instantiated with
    | None, _ -> []
    | Some `Forward, Iff (left, right) ->
        [Extracted.NRConjElimL (kernel_formula (Imp (right, left)))]
    | Some `Backward, Iff (left, right) ->
        [Extracted.NRConjElimR (kernel_formula (Imp (left, right)))]
    | Some _, _ -> verified_error line_no
  in
  projection @ all_commands

let close_fact line_no name context =
  if List.mem_assoc name context then
    (Extracted.NRHypothesis name, [])
  else
    match fixed_axiom_kind (String.lowercase_ascii name) with
    | Some kind ->
        (Extracted.NRAxiom, [Extracted.fixed_axiom kind])
    | None -> verified_error line_no

let close_fact_in_state line_no name state context =
  if List.mem_assoc name context
     || List.mem_assoc name
          (Extracted.environment_facts state.global_environment) then
    (Extracted.NRHypothesis name, [])
  else
    match fixed_axiom_kind (String.lowercase_ascii name) with
    | Some kind ->
        (Extracted.NRAxiom, [Extracted.fixed_axiom kind])
    | None -> verified_error line_no

let parse_choice_words line_no command argument =
  match Rule_parser.term_words argument with
  | witness :: hypothesis :: from_word :: source :: terms
    when String.lowercase_ascii from_word = "from" ->
      (witness, hypothesis, source, terms)
  | _ ->
      raise (Proof_error (line_no,
        Printf.sprintf
          "Use: %s witness hypothesis from fact term1 term2."
          command))

(** Surface [obtain] is an untrusted planner. The extracted certified session
    checks and records the resulting AllElim/ExElim/closing-rule program. *)
let execute_obtain line_no state command argument =
  match materialize_goals line_no state with
  | [] -> raise (Proof_error (line_no, "The proof is already complete."))
  | goal :: _ ->
      let witness, hypothesis, source, terms =
        parse_choice_words line_no command argument
      in
      if List.mem_assoc hypothesis goal.context then
        raise (Proof_error (line_no,
          "A hypothesis with this name already exists."));
      let fact =
        match lookup_fact_in_state state goal.context source with
        | Some fact -> fact
        | None ->
            raise (Proof_error (line_no,
              "Existential fact not found: " ^ source))
      in
      let instantiated, all_rules =
        specialize_rules ~bound:(StringSet.of_list goal.variables)
          line_no state.definitions fact terms
      in
      begin match instantiated with
      | Exists _ ->
          let close_rule, axioms =
            close_fact_in_state line_no source state goal.context
          in
          let program =
            checked_step
              (Extracted.NRExElim
                (witness, hypothesis, kernel_formula instantiated))
            :: List.map checked_step all_rules
            @ [checked_step ~axioms close_rule]
          in
          apply_certificate_program line_no state program
            (command ^ " " ^ witness ^ " " ^ hypothesis
             ^ " from " ^ source)
      | _ ->
          raise (Proof_error (line_no,
            "The selected fact does not become existential after specialization."))
      end

(** Prove the existential selected by a [choose] declaration, replay its
    certificate, and ask the extracted global environment to add the fresh
    constant and fact.  OCaml plans the certificate but never constructs or
    mutates the logical environment itself. *)
let declare_global_choice definitions environment choice =
  let line_no = choice.choose_line in
  let context =
    Extracted.environment_facts environment
    |> List.map (fun (name, formula) ->
         (name, Kernel_syntax.of_kernel formula))
  in
  let fact =
    match lookup_fact choice.choose_source context with
    | Some fact -> fact
    | None ->
        raise (Proof_error (line_no,
          "Existential fact not found: " ^ choice.choose_source))
  in
  let instantiated, all_rules =
    specialize_rules line_no definitions fact choice.choose_terms
  in
  match instantiated with
  | Exists _ ->
      let close_rule, axioms =
            close_fact line_no choice.choose_source context
      in
      let program =
        List.map checked_step all_rules
        @ [checked_step ~axioms close_rule]
      in
      let proof_state =
        Extracted.start_in_environment environment
          (kernel_formula instantiated)
        |> accept_kernel_result line_no "choice source"
        |> kernel_certificate_run line_no program
      in
      if not (Extracted.solved proof_state) then
        raise (Proof_error (line_no,
          "The choice source certificate left unresolved goals."));
      let certificate =
        Extracted.finalize proof_state
        |> accept_kernel_result line_no "choice source certificate replay"
      in
      Extracted.declare_choice
        ~constant:choice.choose_name
        ~fact:choice.choose_fact
        ~source:(kernel_formula instantiated)
        ~proof:certificate
        environment
      |> accept_kernel_result line_no "global choice declaration"
  | _ ->
      raise (Proof_error (line_no,
        "The selected fact does not become existential after specialization."))

let declare_global_skolem environment declaration =
  let line_no = declaration.choose_line in
  let context =
    Extracted.environment_facts environment
    |> List.map (fun (name, formula) ->
         (name, Kernel_syntax.of_kernel formula))
  in
  let source =
    match lookup_fact declaration.choose_source context with
    | Some fact -> fact
    | None ->
        raise (Proof_error (line_no,
          "Universal-existential fact not found: " ^ declaration.choose_source))
  in
  let close_rule, axioms = close_fact line_no declaration.choose_source context in
  let program = [checked_step ~axioms close_rule] in
  let proof_state =
    Extracted.start_in_environment environment (kernel_formula source)
    |> accept_kernel_result line_no "Skolem source"
    |> kernel_certificate_run line_no program
  in
  if not (Extracted.solved proof_state) then
    raise (Proof_error (line_no,
      "The Skolem source certificate left unresolved goals."));
  let certificate =
    Extracted.finalize proof_state
    |> accept_kernel_result line_no "Skolem source certificate replay"
  in
  Extracted.declare_skolem
    ~function_name:declaration.choose_name
    ~fact:declaration.choose_fact
    ~source:(kernel_formula source)
    ~proof:certificate
    environment
  |> accept_kernel_result line_no "global choose declaration"

let context_names context =
  List.fold_left
    (fun names (name, _) -> StringSet.add name names)
    StringSet.empty context

let environment_names state =
  let names =
    Extracted.environment_constants state.global_environment
    |> StringSet.of_list
  in
  List.fold_left
    (fun names (name, _) -> StringSet.add name names)
    names
    (Extracted.environment_facts state.global_environment)

let intro_name_set state goal =
  StringSet.union
    (context_names goal.context)
    (StringSet.union
       (context_free_vars goal.context)
       (StringSet.union
          (all_vars goal.target)
          (environment_names state)))

(* Abstract free occurrences of a whole term, including occurrences nested in
   function arguments.  The caller chooses [binder] fresh for the entire goal;
   substitution by the equality rule then also avoids capture of its endpoints. *)
let abstract_rewrite_term source binder formula =
  let source_variables = term_free_vars source in
  let rec abstract_term term =
    if term = source then Name binder
    else
      match term with
      | Name _ -> term
      | App (name, arguments) ->
          App (name, List.map abstract_term arguments)
  in
  let rec abstract_formula = function
    | Bottom -> Bottom
    | Named (name, arguments) ->
        Named (name, List.map abstract_term arguments)
    | Eq (left, right) -> Eq (abstract_term left, abstract_term right)
    | Mem (left, right) -> Mem (abstract_term left, abstract_term right)
    | Not body -> Not (abstract_formula body)
    | And (left, right) -> And (abstract_formula left, abstract_formula right)
    | Or (left, right) -> Or (abstract_formula left, abstract_formula right)
    | Imp (left, right) -> Imp (abstract_formula left, abstract_formula right)
    | Iff (left, right) -> Iff (abstract_formula left, abstract_formula right)
    | (Forall (name, _) | Exists (name, _)) as quantified
        when StringSet.mem name source_variables -> quantified
    | Forall (name, body) -> Forall (name, abstract_formula body)
    | Exists (name, body) -> Exists (name, abstract_formula body)
  in
  abstract_formula formula

let execute_separation line_no state fact_name source element predicate =
  let kernel_state =
    Extracted.separation_term_tactic_step
      ~fact:fact_name
      ~source:(Kernel_syntax.to_kernel_term source)
      ~element
      (kernel_formula predicate)
      state.kernel_state
    |> accept_kernel_result line_no "separation tactic"
  in
  add_step state ("separation " ^ fact_name) kernel_state

let execute_resolution line_no state goal argument =
  if trim argument <> "" then
    raise (Proof_error (line_no, "resolution takes no arguments."));
  let program =
    match Resolution.plan goal.context goal.target with
    | Ok program -> program
    | Error message -> raise (Proof_error (line_no, message))
  in
  apply_certificate_program line_no state program "resolution"

let execute_put line_no state argument =
  let name = trim argument in
  if name = "" || String.contains name ' ' || String.contains name '\t' then
    raise (Proof_error (line_no, "Use: put theorem_name."));
  if StringSet.mem name state.put_facts then
    raise (Proof_error (line_no,
      "Global fact " ^ name ^ " is already in the current context."));
  if
    not
      (List.exists
         (fun (fact_name, _) -> fact_name = name)
         (Extracted.environment_facts state.global_environment))
  then
    raise (Proof_error (line_no, "Global fact not found: " ^ name));
  if not (StringSet.mem name state.hidden_global_facts) then
    raise (Proof_error (line_no,
      "Global fact " ^ name ^ " is already in the current context."));
  { state with
    put_facts = StringSet.add name state.put_facts;
    final_certificate = None;
    steps = ("put " ^ name) :: state.steps;
  }

let fresh_intro_name base used =
  if StringSet.mem base used then fresh_name base used else base

let execute_intro line_no state argument =
  let argument = trim argument in
  if argument <> "" && not (valid_term_name argument) then
    raise (Proof_error (line_no,
      "intro accepts exactly one identifier; use intros x y. for multiple introductions."));
  match materialize_goals line_no state with
  | [] -> raise (Proof_error (line_no, "The proof is already complete."))
  | goal :: _ ->
      begin match goal.target with
      | Imp _ | Not _ ->
          if argument = "" then
            raise (Proof_error (line_no, "Expected a hypothesis name."));
          apply_primitive_rules line_no state
            [Extracted.NRImplIntro argument]
            ("intro " ^ argument)
      | Forall (x, _) ->
          let chosen = if argument = "" then x else argument in
          if StringSet.mem chosen (context_free_vars goal.context) then
            raise (Proof_error (line_no,
              "The introduced variable occurs free in a hypothesis."));
          apply_primitive_rules line_no state
            [Extracted.NRAllIntro chosen]
            ("intro " ^ chosen)
      | _ ->
          raise (Proof_error (line_no,
            "intro requires an implication, negation, or universal goal."))
      end

let auto_intro_name line_no state goal =
  let used = intro_name_set state goal in
  match goal.target with
  | Forall (binder, _) ->
      let forbidden =
        StringSet.union
          (context_names goal.context)
          (StringSet.union
             (context_free_vars goal.context)
             (environment_names state))
      in
      if StringSet.mem binder forbidden then fresh_name binder used else binder
  | Imp _ | Not _ -> fresh_intro_name "H" used
  | _ ->
      raise (Proof_error (line_no,
        "intros has no introductions left."))

let execute_intros line_no state argument =
  let names = words argument in
  let rec introduce_named state = function
    | [] -> state
    | name :: rest ->
        introduce_named (execute_intro line_no state name) rest
  in
  if names <> [] then
    introduce_named state names
  else
    let rec introduce_automatically state =
      match materialize_goals line_no state with
      | [] -> state
      | goal :: _ ->
          begin match goal.target with
          | Imp _ | Not _ | Forall _ ->
              let name = auto_intro_name line_no state goal in
              introduce_automatically (execute_intro line_no state name)
          | _ -> state
          end
    in
    introduce_automatically state

let execute_tactic line_no state line =
  match materialize_goals line_no state with
  | [] -> raise (Proof_error (line_no, "The proof is already complete."))
  | goal :: _ ->
      let command, argument = split_first_word line in
      let command = String.lowercase_ascii command in
      let bound = StringSet.of_list goal.variables in
      begin match command with
      | "rule" -> execute_rule line_no state argument
      | "put" -> execute_put line_no state argument
      | "obtain" -> execute_obtain line_no state "obtain" argument
      | "resolution" -> execute_resolution line_no state goal argument
      | "separation" ->
          let fact_name, source, element, predicate =
            parse_separation_argument line_no state.aliases state.definitions
              state.global_environment bound argument
          in
          execute_separation line_no state
            fact_name source element predicate
      | "replacement" ->
          let names, predicate =
            split_schema_argument line_no state.aliases state.definitions
              state.global_environment bound argument
          in
          begin match names with
          | [fact_name; source; input; output] ->
              if source = input || input = output || source = output then
                raise (Proof_error (line_no,
                  "The source, input, and output variables must have distinct names."));
              let kernel_state =
                Extracted.replacement_tactic_step
                  ~fact:fact_name ~source ~input ~output
                  (kernel_formula predicate) state.kernel_state
                |> accept_kernel_result line_no "replacement tactic"
              in
              add_step state ("replacement " ^ fact_name) kernel_state
          | _ ->
              raise (Proof_error (line_no,
                "Use: replacement R source x y : P."))
          end
      | "intro" -> execute_intro line_no state argument
      | "intros" -> execute_intros line_no state argument
      | "assumption" ->
          let rec find = function
            | [] -> None
            | (name, f) :: _ when alpha_equal f goal.target -> Some name
            | _ :: tail -> find tail
          in
          begin match find goal.context with
          | Some name ->
              apply_primitive_rules line_no state
                [Extracted.NRHypothesis name] "assumption"
          | None ->
              raise (Proof_error (line_no,
                "No hypothesis matches the current goal."))
          end
      | "exact" ->
          begin match lookup_fact_in_state state goal.context argument with
          | None ->
              raise (Proof_error (line_no,
                "Fact not found: " ^ argument))
          | Some fact when alpha_equal fact goal.target ->
              let rule, axioms =
                close_fact_in_state line_no argument
                  state goal.context
              in
              apply_certificate_program line_no state
                [checked_step ~axioms rule]
                ("exact " ^ argument)
          | Some _ ->
              raise (Proof_error (line_no,
                "The type of " ^ argument ^ " does not match the current goal."))
          end
      | "apply" ->
          let direction, apply_words =
            match words argument with
            | "->" :: rest -> (Some `Forward, rest)
            | "<-" :: rest -> (Some `Backward, rest)
            | rest -> (None, rest)
          in
          let application =
            "apply " ^
            (match direction with
             | None -> ""
             | Some `Forward -> "-> "
             | Some `Backward -> "<- ")
          in
          let decompose_fact fact =
            match decompose_apply_fact direction fact with
            | Ok parts -> parts
            | Error message -> raise (Proof_error (line_no, message))
          in
          begin match apply_words with
          | [fact_name; in_word; source_name; as_word; new_name]
              when String.lowercase_ascii in_word = "in"
                   && String.lowercase_ascii as_word = "as" ->
              if new_name = "" then
                raise (Proof_error (line_no,
                  "Expected a name after apply ... in ... as."));
              if List.mem_assoc new_name goal.context then
                raise (Proof_error (line_no,
                  "A hypothesis with this name already exists."));
              let source_formula =
                match lookup_assumption state goal.context source_name with
                | Some formula -> formula
                | None ->
                    raise (Proof_error (line_no,
                      "Hypothesis not found: " ^ source_name))
              in
              begin match lookup_fact_in_state state goal.context fact_name with
              | None ->
                  raise (Proof_error (line_no,
                    "Theorem, hypothesis, or axiom not found: " ^ fact_name))
              | Some fact ->
                  let metas, premises, conclusion = decompose_fact fact in
                  begin match premises with
                  | [premise] ->
                      begin match match_formula metas premise source_formula with
                      | None ->
                          raise (Proof_error (line_no,
                            "The selected hypothesis does not match the premise of "
                            ^ fact_name ^ "."))
                      | Some substitutions ->
                          begin match unresolved_instantiations metas substitutions with
                          | name :: rest ->
                              raise (Proof_error (line_no,
                                cannot_infer_instantiations (name :: rest)))
                          | [] ->
                          let instantiated_premise =
                            instantiate_formula substitutions premise
                          in
                          let instantiated_conclusion =
                            instantiate_formula substitutions conclusion
                          in
                          let fact_commands =
                            apply_fact_rules ~bound line_no state.definitions
                              direction fact substitutions
                          in
                          let close_command, axioms =
                            close_fact_in_state line_no fact_name
                              state goal.context
                          in
                          let program =
                            [checked_step
                               (Extracted.NRCut
                                  (new_name,
                                   kernel_formula instantiated_conclusion));
                             checked_step
                               (Extracted.NRImplElim
                                  (kernel_formula instantiated_premise))]
                            @ List.map checked_step fact_commands
                            @ [checked_step ~axioms close_command;
                               checked_step
                                 (Extracted.NRHypothesis source_name)]
                          in
                          apply_certificate_program line_no state program
                            (application ^ fact_name ^ " in " ^ source_name
                             ^ " as " ^ new_name)
                          end
                      end
                  | _ ->
                      raise (Proof_error (line_no,
                        "apply ... in ... as currently requires a fact with "
                        ^ "exactly one implication premise."))
                  end
              end
          | [fact_name] ->
              begin match lookup_fact_in_state state goal.context fact_name with
              | None ->
                  raise (Proof_error (line_no,
                    "Theorem, hypothesis, or axiom not found: " ^ fact_name))
              | Some fact ->
                  begin match apply_fact (decompose_fact fact) goal with
                  | Error message -> raise (Proof_error (line_no, message))
                  | Ok (premises, substitutions) ->
                      let fact_commands =
                        apply_fact_rules ~bound line_no state.definitions
                          direction fact substitutions
                      in
                      let implication_commands =
                        List.rev premises
                        |> List.map (fun premise ->
                             Extracted.NRImplElim (kernel_formula premise))
                      in
                      let close_command, axioms =
                        close_fact_in_state line_no fact_name
                          state goal.context
                      in
                      let program =
                        List.map checked_step
                          (implication_commands @ fact_commands)
                        @ [checked_step ~axioms close_command]
                      in
                      apply_certificate_program line_no state program
                        (application ^ fact_name)
                  end
              end
          | _ ->
              raise (Proof_error (line_no,
                "Use apply [->|<-] H or apply [->|<-] H0 in H as H1."))
          end
      | "rewrite" ->
          let direction, equality_name =
            match words argument with
            | [equality_name] -> (`Forward, equality_name)
            | [arrow; equality_name] when arrow = "<-" ->
                (`Backward, equality_name)
            | _ ->
                raise (Proof_error (line_no,
                  "Use rewrite H or rewrite <- H."))
          in
          begin match direction with
          | (`Forward | `Backward) ->
              let left, right =
                match lookup_assumption state goal.context equality_name with
                | Some (Eq (left, right)) -> (left, right)
                | Some _ ->
                    raise (Proof_error (line_no,
                      "rewrite requires an equality hypothesis."))
                | None ->
                    raise (Proof_error (line_no,
                      "Hypothesis not found: " ^ equality_name))
              in
              let used =
                StringSet.union
                  (intro_name_set state goal)
                  (StringSet.union
                     (StringSet.of_list goal.variables)
                     (StringSet.union
                        (term_free_vars left) (term_free_vars right)))
              in
              let binder = fresh_name "rewrite_var" used in
              let source =
                match direction with
                | `Forward -> left
                | `Backward -> right
              in
              let predicate_body =
                abstract_rewrite_term source binder goal.target
              in
              let predicate = Forall (binder, predicate_body) in
              let symmetry_predicate =
                Forall (binder, Eq (Name binder, left))
              in
              let kernel_left = Kernel_syntax.to_kernel_term left in
              let kernel_right = Kernel_syntax.to_kernel_term right in
              let description =
                match direction with
                | `Forward -> "rewrite " ^ equality_name
                | `Backward -> "rewrite <- " ^ equality_name
              in
              let program =
                match direction with
                | `Forward ->
                    [ checked_step
                        (Extracted.NREqualElim
                           (kernel_right, kernel_left,
                            kernel_formula predicate));
                      checked_step
                        (Extracted.NREqualElim
                           (kernel_left, kernel_right,
                            kernel_formula symmetry_predicate));
                      checked_step (Extracted.NRHypothesis equality_name);
                      checked_step Extracted.NREqualRefl ]
                | `Backward ->
                    [ checked_step
                        (Extracted.NREqualElim
                           (kernel_left, kernel_right,
                            kernel_formula predicate));
                      checked_step (Extracted.NRHypothesis equality_name) ]
              in
              apply_certificate_program line_no state program
                description
          end
      | "specialize" ->
          let words = Rule_parser.term_words argument in
          let rec split_as before = function
            | ["as"; new_name] -> (List.rev before, new_name)
            | "as" :: _ ->
                raise (Proof_error (line_no,
                  "Use: specialize H a as H_a."))
            | word :: rest -> split_as (word :: before) rest
            | [] ->
                raise (Proof_error (line_no,
                  "Expected a name for the specialized fact after as."))
          in
          let source_and_terms, new_name = split_as [] words in
          begin match source_and_terms with
          | source :: terms when terms <> [] ->
              if List.mem_assoc new_name goal.context then
                raise (Proof_error (line_no,
                  "A hypothesis with this name already exists."));
              let fact =
                match lookup_fact_in_state state goal.context source with
                | Some fact -> fact
                | None ->
                    raise (Proof_error (line_no,
                      "Universally quantified fact not found: " ^ source))
              in
              let instantiated, all_commands =
                specialize_rules ~bound line_no state.definitions fact terms
              in
              let close_command, axioms =
                close_fact_in_state line_no source state goal.context
              in
              let prefix =
                Extracted.NRCut
                  (new_name, kernel_formula instantiated) ::
                all_commands
              in
              let program =
                List.map checked_step prefix
                @ [checked_step ~axioms close_command]
              in
              apply_certificate_program line_no state program
                ("specialize " ^ source ^ " as " ^ new_name)
          | _ ->
              raise (Proof_error (line_no,
                "Use specialize H term... as name with at least one term."))
          end
      | "cases" ->
          let words = words argument in
          begin match words with
          | fact_name :: names ->
              begin match lookup_assumption state goal.context fact_name with
              | None ->
                  raise (Proof_error (line_no,
                    "Hypothesis not found: " ^ fact_name))
              | Some (And (left_formula, right_formula)) ->
                  let left_name, right_name =
                    match names with
                    | [left_name; right_name] -> (left_name, right_name)
                    | [] -> (fact_name ^ "_left", fact_name ^ "_right")
                    | _ ->
                        raise (Proof_error (line_no,
                          "Use cases H H1 H2 for conjunctions and equivalences."))
                  in
                  if List.mem_assoc left_name goal.context || List.mem_assoc right_name goal.context then
                    raise (Proof_error (line_no,
                      "Case hypotheses must use fresh names."));
                  apply_primitive_rules line_no state
                    [ Extracted.NRCut
                        (left_name, kernel_formula left_formula);
                      Extracted.NRConjElimL
                        (kernel_formula right_formula);
                      Extracted.NRHypothesis fact_name;
                      Extracted.NRCut
                        (right_name, kernel_formula right_formula);
                      Extracted.NRConjElimR
                        (kernel_formula left_formula);
                      Extracted.NRHypothesis fact_name
                    ]
                    ("cases " ^ fact_name)
              | Some (Iff (left_formula, right_formula)) ->
                  let forward_name, backward_name =
                    match names with
                    | [forward_name; backward_name] -> (forward_name, backward_name)
                    | [] -> (fact_name ^ "_forward", fact_name ^ "_backward")
                    | _ ->
                        raise (Proof_error (line_no,
                          "Use cases H H1 H2 for conjunctions and equivalences."))
                  in
                  if List.mem_assoc forward_name goal.context || List.mem_assoc backward_name goal.context then
                    raise (Proof_error (line_no,
                      "Case hypotheses must use fresh names."));
                  let forward = Imp (left_formula, right_formula) in
                  let backward = Imp (right_formula, left_formula) in
                  apply_primitive_rules line_no state
                    [ Extracted.NRCut
                        (forward_name, kernel_formula forward);
                      Extracted.NRConjElimL
                        (kernel_formula backward);
                      Extracted.NRHypothesis fact_name;
                      Extracted.NRCut
                        (backward_name, kernel_formula backward);
                      Extracted.NRConjElimR
                        (kernel_formula forward);
                      Extracted.NRHypothesis fact_name
                    ]
                    ("cases " ^ fact_name)
              | Some (Or (left_formula, right_formula)) ->
                  let left_name, right_name =
                    match names with
                    | [left_name; right_name] -> (left_name, right_name)
                    | [] -> (fact_name ^ "_left", fact_name ^ "_right")
                    | _ ->
                        raise (Proof_error (line_no,
                          "Use cases H H1 H2 for conjunctions, disjunctions, and equivalences."))
                  in
                  if List.mem_assoc left_name goal.context
                     || List.mem_assoc right_name goal.context
                  then
                    raise (Proof_error (line_no,
                      "Case hypotheses must use fresh names."));
                  apply_primitive_rules line_no state
                    [ Extracted.NRDisjElim
                        (kernel_formula left_formula,
                         kernel_formula right_formula,
                         left_name, right_name);
                      Extracted.NRHypothesis fact_name
                    ]
                    ("cases " ^ fact_name)
              | Some ((Exists _) as existential) ->
                  let witness, hypothesis =
                    match names with
                    | [witness; hypothesis] -> (witness, hypothesis)
                    | _ ->
                        raise (Proof_error (line_no,
                          "Use cases H witness Hw for an existential hypothesis."))
                  in
                  let forbidden =
                    StringSet.union (context_free_vars goal.context) (free_vars goal.target)
                  in
                  if StringSet.mem witness forbidden then
                    raise (Proof_error (line_no,
                      "The existential witness must be fresh in the context and goal."));
                  if List.mem_assoc hypothesis goal.context then
                    raise (Proof_error (line_no,
                      "The eliminated hypothesis must use a fresh name."));
                  apply_primitive_rules line_no state
                    [ Extracted.NRExElim
                        (witness, hypothesis, kernel_formula existential);
                      Extracted.NRHypothesis fact_name
                    ]
                    ("cases " ^ fact_name)
              | Some _ ->
                  raise (Proof_error (line_no,
                    "cases requires a conjunction, disjunction, equivalence, or existential hypothesis."))
              end
          | [] ->
              raise (Proof_error (line_no,
                "Expected the name of a hypothesis to eliminate."))
          end
      | "refl" ->
          begin match goal.target with
          | Eq (a, b) when a = b ->
              apply_primitive_rules line_no state [Extracted.NREqualRefl]
                "refl"
          | _ ->
              raise (Proof_error (line_no,
                "refl requires a goal of the form t = t."))
          end
      | "split" | "constructor" ->
          begin match goal.target with
          | And _ | Iff _ ->
              apply_primitive_rules line_no state [Extracted.NRConjIntro]
                "split"
          | _ ->
              raise (Proof_error (line_no,
                "split requires a conjunction or equivalence goal."))
          end
      | "left" ->
          begin match goal.target with
          | Or _ ->
              apply_primitive_rules line_no state [Extracted.NRDisjIntroL]
                "left"
          | _ ->
              raise (Proof_error (line_no,
                "left requires a disjunction goal."))
          end
      | "right" ->
          begin match goal.target with
          | Or _ ->
              apply_primitive_rules line_no state [Extracted.NRDisjIntroR]
                "right"
          | _ ->
              raise (Proof_error (line_no,
                "right requires a disjunction goal."))
          end
      | "use" ->
          if argument = "" then
            raise (Proof_error (line_no,
              "Expected a variable to use as the existential witness."));
          begin match goal.target with
          | Exists _ ->
              let witness = parse_surface_term ~bound line_no state.definitions argument in
              apply_primitive_rules line_no state
                [Extracted.NRExIntro (Kernel_syntax.to_kernel_term witness)]
                ("use " ^ argument)
          | _ ->
              raise (Proof_error (line_no,
                "use requires an existential goal."))
          end
      | "contradiction" ->
          let bottom =
            List.find_opt
              (fun (_, formula) -> alpha_equal formula Bottom)
              goal.context
          in
          begin match bottom with
          | Some (name, _) ->
              apply_primitive_rules line_no state
                [ Extracted.NRFalsumElim;
                  Extracted.NRHypothesis name
                ]
                "contradiction"
          | None ->
              let rec find_pair = function
                | [] -> None
                | (negative_name, Not premise) :: rest ->
                    begin match
                      List.find_opt
                        (fun (_, formula) -> alpha_equal formula premise)
                        goal.context
                    with
                    | Some (positive_name, _) ->
                        Some (negative_name, positive_name, premise)
                    | None -> find_pair rest
                    end
                | _ :: rest -> find_pair rest
              in
              begin match find_pair goal.context with
              | Some (negative_name, positive_name, premise) ->
                  apply_primitive_rules line_no state
                    [ Extracted.NRFalsumElim;
                      Extracted.NRImplElim (kernel_formula premise);
                      Extracted.NRHypothesis negative_name;
                      Extracted.NRHypothesis positive_name
                    ]
                    "contradiction"
              | None ->
                  raise (Proof_error (line_no,
                    "No contradictory hypotheses were found."))
              end
          end
      | _ ->
          raise (Proof_error (line_no, "Unknown tactic: " ^ command))
      end

let find_colon s =
  match String.index_opt s ':' with
  | Some i -> i
  | None -> raise (Parse_error (0, "A theorem declaration requires :."))

let valid_alias_name name =
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

let parse_alias line_no aliases definitions environment line =
  let prefix = "alias " in
  let content =
    trim (String.sub line (String.length prefix)
      (String.length line - String.length prefix))
  in
  let assignment =
    match find_assignment content with
    | Some index -> index
    | None ->
        raise (Proof_error (line_no,
          "Use: alias name parameters... := formula."))
  in
  let declaration =
    String.sub content 0 assignment
    |> trim
    |> words
  in
  let name, parameters =
    match declaration with
    | name :: parameters -> (name, parameters)
    | [] -> raise (Proof_error (line_no, "Expected an alias name."))
  in
  if not (valid_alias_name name) then
    raise (Proof_error (line_no, "Invalid alias name: " ^ name));
  if Option.is_some (find_alias name aliases) then
    raise (Proof_error (line_no,
      "Proposition alias already exists: " ^ name));
  let constants =
    StringSet.of_list (Extracted.environment_constants environment)
  in
  List.iter
    (fun parameter ->
       if not (valid_alias_name parameter) then
         raise (Proof_error (line_no,
           "Invalid alias parameter: " ^ parameter));
       if StringSet.mem parameter constants then
         raise (Proof_error (line_no,
           "Alias parameter conflicts with a declared constant: " ^ parameter)))
    parameters;
  let parameter_set = StringSet.of_list parameters in
  if StringSet.cardinal parameter_set <> List.length parameters then
    raise (Proof_error (line_no, "Alias parameters must be unique."));
  let statement =
    String.sub content (assignment + 2)
      (String.length content - assignment - 2)
    |> drop_optional_final_dot
  in
  if statement = "" then
    raise (Proof_error (line_no, "Expected a formula after :=."));
  let body =
    try parse_formula statement |> unfold ~bound:parameter_set line_no aliases definitions environment
    with Parse_error (_, message) -> raise (Proof_error (line_no, message))
  in
  let allowed = StringSet.union parameter_set constants in
  let undeclared = StringSet.diff (free_vars body) allowed in
  if not (StringSet.is_empty undeclared) then begin
    let variables = String.concat ", " (StringSet.elements undeclared) in
    raise (Proof_error (line_no,
      "Undeclared free variables in alias body: " ^ variables))
  end else
    aliases @ [{
      alias_name = name;
      parameters;
      body;
    }]

let parse_definition line_no definitions environment line =
  let _, content = split_first_word line in
  let assignment =
    match find_assignment content with
    | Some index -> index
    | None -> raise (Proof_error (line_no,
        "Use: definition f(x, y) := term."))
  in
  let declaration = trim (String.sub content 0 assignment) in
  let head =
    try Parser.parse_term declaration
    with Parse_error (_, message) -> raise (Proof_error (line_no, message))
  in
  let name, parameters =
    match head with
    | Name name -> (name, [])
    | App (name, arguments) ->
        let parameters = List.map (function
          | Name parameter -> parameter
          | App _ -> raise (Proof_error (line_no,
              "Definition parameters must be variable names."))) arguments
        in
        (name, parameters)
  in
  if not (valid_alias_name name) then
    raise (Proof_error (line_no, "Invalid definition name: " ^ name));
  if Option.is_some (find_definition name definitions) then
    raise (Proof_error (line_no, "Term definition already exists: " ^ name));
  let constants =
    StringSet.of_list (Extracted.environment_constants environment)
  in
  if StringSet.mem name constants then
    raise (Proof_error (line_no,
      "Definition name conflicts with a declared constant or function: " ^ name));
  List.iter (fun parameter ->
    if not (valid_alias_name parameter) then
      raise (Proof_error (line_no, "Invalid definition parameter: " ^ parameter));
    if StringSet.mem parameter constants then
      raise (Proof_error (line_no,
        "Definition parameter conflicts with a declared constant: " ^ parameter)))
    parameters;
  let parameter_set = StringSet.of_list parameters in
  if StringSet.cardinal parameter_set <> List.length parameters then
    raise (Proof_error (line_no, "Definition parameters must be unique."));
  let text = trim (String.sub content (assignment + 2)
    (String.length content - assignment - 2)) in
  if text = "" then
    raise (Proof_error (line_no, "Expected a term after :=."));
  let raw_body =
    try Parser.parse_term text
    with Parse_error (_, message) -> raise (Proof_error (line_no, message))
  in
  (* Check every source argument, even if the referenced definition discards
     that parameter and the argument disappears during expansion. *)
  let check_symbol symbol arguments is_variable =
    if symbol = name then
      raise (Proof_error (line_no, "Recursive term definition: " ^ name));
    match find_definition symbol definitions with
    | Some definition -> check_definition_arity line_no definition arguments
    | None when StringSet.mem symbol constants -> ()
    | None ->
        raise (Proof_error (line_no,
          (if is_variable then "Undeclared free variables in definition body: "
           else "Undefined function name in definition body: ") ^ symbol))
  in
  let rec check_body = function
    | Name variable when StringSet.mem variable parameter_set -> ()
    | Name variable -> check_symbol variable [] true
    | App (function_name, arguments) ->
        check_symbol function_name arguments false;
        List.iter check_body arguments
  in
  check_body raw_body;
  let body = unfold_term line_no definitions parameter_set raw_body in
  let undeclared = StringSet.diff (term_free_vars body)
    (StringSet.union parameter_set constants) in
  if not (StringSet.is_empty undeclared) then
    raise (Proof_error (line_no,
      "Undeclared free variables in definition body: "
      ^ String.concat ", " (StringSet.elements undeclared)));
  (* Validate the expanded function heads with the same extracted elaborator
     used for theorem statements, without extending the logical environment. *)
  let validation = List.fold_right (fun parameter body -> Forall (parameter, body))
    parameters (Eq (body, body)) in
  ignore (Extracted.start_in_environment environment (kernel_formula validation)
    |> accept_kernel_result line_no "definition body");
  definitions @ [{ definition_name = name; parameters; body }]

let analyze_statements meaningful =
  let apply_choice definitions environment steps declaration =
    let context =
      Extracted.environment_facts environment
      |> List.map (fun (name, formula) ->
           (name, Kernel_syntax.of_kernel formula))
    in
    let source_is_universal =
      match lookup_fact declaration.choose_source context with
      | Some (Forall _) -> true
      | _ -> false
    in
    let environment =
      if declaration.choose_terms = [] && source_is_universal
      then declare_global_skolem environment declaration
      else declare_global_choice definitions environment declaration
    in
    let description =
      String.concat " "
        ("choose" :: declaration.choose_name ::
         declaration.choose_fact :: "from" ::
         declaration.choose_source :: declaration.choose_terms)
    in
    (environment, description :: steps)
  in
  (* Apply choices in source order so aliases see only constants that have
     already been certified in the global environment. *)
  let rec read_declarations aliases definitions environment steps declarations = function
    | (line_no, line) :: rest
      when starts_with_at (String.lowercase_ascii line) 0 "alias " ->
        read_declarations
          (parse_alias line_no aliases definitions environment line)
          definitions environment steps declarations rest
    | (line_no, line) :: rest
      when String.lowercase_ascii (fst (split_first_word line)) = "definition" ->
        read_declarations aliases
          (parse_definition line_no definitions environment line)
          environment steps declarations rest
    | (line_no, line) :: rest
      when starts_with_at (String.lowercase_ascii line) 0 "choose " ->
        let prefix = "choose " in
        let argument =
          trim (String.sub line (String.length prefix)
            (String.length line - String.length prefix))
        in
        let name, fact, source, terms =
          parse_choice_words line_no "choose" argument
        in
        if Option.is_some (find_definition name definitions) then
          raise (Proof_error (line_no,
            "choose name conflicts with a term definition: " ^ name));
        let declaration = {
          choose_line = line_no;
          choose_name = name;
          choose_fact = fact;
          choose_source = source;
          choose_terms = terms;
        } in
        let environment, steps = apply_choice definitions environment steps declaration in
        read_declarations aliases definitions environment steps
          (declarations @ [declaration]) rest
    | (line_no, line) :: _rest
      when starts_with_at (String.lowercase_ascii line) 0 "skolem " ->
        raise (Proof_error (line_no,
          "The Skolem keyword has been removed; use choose f H from fact."))
    | rest -> (aliases, definitions, environment, steps, declarations, rest)
  in
  let rec process hidden_facts aliases definitions environment steps statements =
    let aliases, definitions, global_environment, declaration_steps, declarations, proof =
      read_declarations aliases definitions environment steps [] statements
    in
    (* A [choose] declaration is a global declaration, not an automatic
       hypothesis of the theorem that follows it.  Keep its certified fact in
       the extracted environment so that it can still be used as a source by
       later declarations, but hide it from the surface proof context and
       resolution search until the user explicitly writes [put]. *)
    let hidden_facts =
      List.fold_left
        (fun hidden declaration ->
           StringSet.add declaration.choose_fact hidden)
        hidden_facts declarations
    in
    match proof with
    | [] when aliases <> [] || definitions <> [] || declarations <> [] ->
        let kernel_state =
          Extracted.start_in_environment global_environment Extracted.NFalsum
          |> accept_kernel_result 1 "initial goal"
        in
        let declarations = {
          theorem_name = "";
          theorem = Bottom;
          aliases;
          definitions;
          global_environment;
          hidden_global_facts = hidden_facts;
          put_facts = StringSet.empty;
          kernel_state;
          final_certificate = None;
          steps = declaration_steps;
        } in
        (declarations, false)
    | [] -> raise (Proof_error (1, "The proof script is empty."))
    | (header_line, header) :: tactics ->
        let lower_header = String.lowercase_ascii header in
        let prefix = "theorem " in
        if not (starts_with_at lower_header 0 prefix) then
          raise (Proof_error (header_line,
            "After aliases, definitions and choose declarations, use: theorem name : formula."));
        let content = trim (String.sub header (String.length prefix) (String.length header - String.length prefix)) in
        let colon =
          try find_colon content
          with Parse_error (_, message) -> raise (Proof_error (header_line, message))
        in
        let name = trim (String.sub content 0 colon) in
        let statement = trim (String.sub content (colon + 1) (String.length content - colon - 1)) in
        if name = "" then
          raise (Proof_error (header_line, "Expected a theorem name."));
        let theorem =
          try parse_formula statement |> unfold header_line aliases definitions global_environment
          with Parse_error (_, message) -> raise (Proof_error (header_line, message))
        in
        let kernel_state =
          Extracted.start_in_environment global_environment
            (kernel_formula theorem)
          |> accept_kernel_result header_line "initial goal"
        in
        let initial = {
          theorem_name = name;
          theorem;
          aliases;
          definitions;
          global_environment;
          hidden_global_facts = hidden_facts;
          put_facts = StringSet.empty;
          kernel_state;
          final_certificate = None;
          steps = declaration_steps;
        } in
        let rec run state = function
          | [] -> (state, false)
          | (line_no, line) :: rest
            when String.lowercase_ascii line = "qed" ->
              if not (Extracted.solved state.kernel_state) then
                raise (Proof_error (line_no,
                  "qed cannot close a proof with unresolved goals."));
              if rest = [] then
                let certificate =
                  Extracted.finalize state.kernel_state
                  |> accept_kernel_result line_no "final certificate replay"
                in
                ({ state with final_certificate = Some certificate }, true)
              else
                let next_environment, certificate =
                  Extracted.declare_session_fact
                    ~fact:state.theorem_name
                    ~source:(kernel_formula state.theorem)
                    state.kernel_state
                    state.global_environment
                  |> accept_kernel_result line_no "global theorem declaration"
                in
                let state = { state with final_certificate = Some certificate } in
                process
                  (StringSet.add state.theorem_name hidden_facts)
                  aliases definitions next_environment state.steps rest
          | (line_no, line) :: rest ->
              run (execute_tactic line_no state line) rest
        in
        run initial tactics
  in
  process StringSet.empty [] [] Extracted.empty_environment [] meaningful

let prepare_script ?filename ?load_input script =
  try Script_input.expand ?filename ?load_input script with
  | Script_input.Error (line, message) -> raise (Proof_error (line, message))

let with_source source evaluate =
  if Script_input.statements source = [] then evaluate ()
  else try evaluate () with
  | Proof_error (line, message) ->
      let line, message = Script_input.error source line message in
      raise (Proof_error (line, message))

let analyze_script ?filename ?load_input script =
  let source = prepare_script ?filename ?load_input script in
  with_source source (fun () ->
    analyze_statements (Script_input.statements source))

let check_script ?filename ?load_input script =
  let source = prepare_script ?filename ?load_input script in
  with_source source (fun () ->
    let state, _ = analyze_statements (Script_input.statements source) in
    if state.theorem_name = "" then state
    else if Extracted.solved state.kernel_state then
      begin match state.final_certificate with
      | Some _ -> state
      | None ->
          let line = Script_input.end_line source in
          let certificate =
            Extracted.finalize state.kernel_state
            |> accept_kernel_result line "final certificate replay"
          in
          { state with final_certificate = Some certificate }
      end
    else
      let line = Script_input.end_line source in
      raise (Proof_error (line, "The proof has unresolved goals.")))

let theorem_name state = state.theorem_name
let theorem state = state.theorem
let aliases state = state.aliases
let definitions state = state.definitions
let global_constants state =
  Extracted.environment_constants state.global_environment
let global_facts state =
  Extracted.environment_facts state.global_environment
  |> List.map (fun (name, formula) ->
       (name, Kernel_syntax.of_kernel formula))

type display_goal = {
  variables : string list;
  context : (string * formula) list;
  target : formula;
}

let goals state =
  if state.theorem_name = "" then []
  else
    materialize_goals 1 state
    |> List.map
         (fun (goal : goal) ->
            ({
              variables = goal.variables;
              context = goal.context;
              target = goal.target;
            } : display_goal))
let step_count state = List.length state.steps
let is_complete state = Extracted.solved state.kernel_state

let display_kernel_formula formula =
  formula
  |> Kernel_syntax.of_kernel
  |> formula_to_string

let rec display_kernel_term = function
  | Extracted.NName name -> name
  | Extracted.NApp (name, arguments) ->
      let rec display_arguments = function
        | Extracted.NNNil -> []
        | Extracted.NNCons (argument, rest) ->
            display_kernel_term argument :: display_arguments rest
      in
      name ^ "(" ^ String.concat ", " (display_arguments arguments) ^ ")"

let display_rule = function
  | Extracted.NRAxiom -> "axiom"
  | Extracted.NRHypothesis name -> "hypothesis " ^ name
  | Extracted.NRFalsumElim -> "falsum_elim"
  | Extracted.NRImplIntro name -> "impl_intro " ^ name
  | Extracted.NRImplElim premise ->
      "impl_elim : " ^ display_kernel_formula premise
  | Extracted.NRConjIntro -> "conj_intro"
  | Extracted.NRConjElimL right ->
      "conj_elim_l : " ^ display_kernel_formula right
  | Extracted.NRConjElimR left ->
      "conj_elim_r : " ^ display_kernel_formula left
  | Extracted.NRDisjIntroL -> "disj_intro_l"
  | Extracted.NRDisjIntroR -> "disj_intro_r"
  | Extracted.NRDisjElim (left, right, left_name, right_name) ->
      Printf.sprintf "disj_elim %s %s : %s ; %s"
        left_name right_name
        (display_kernel_formula left)
        (display_kernel_formula right)
  | Extracted.NRAllIntro variable -> "all_intro " ^ variable
  | Extracted.NRAllElim (term, universal) ->
      Printf.sprintf "all_elim %s : %s"
        (display_kernel_term term) (display_kernel_formula universal)
  | Extracted.NRExIntro term -> "ex_intro " ^ display_kernel_term term
  | Extracted.NRExElim (witness, hypothesis, existential) ->
      Printf.sprintf "ex_elim %s %s : %s"
        witness hypothesis (display_kernel_formula existential)
  | Extracted.NREqualRefl -> "equal_refl"
  | Extracted.NREqualElim (left, right, predicate) ->
      Printf.sprintf "equal_elim %s %s : %s"
        (display_kernel_term left) (display_kernel_term right)
        (display_kernel_formula predicate)
  | Extracted.NRCut (hypothesis, lemma) ->
      Printf.sprintf "cut %s : %s"
        hypothesis (display_kernel_formula lemma)

let certificate_rules state =
  Option.map
    (fun certificate ->
       Extracted.certificate_rules certificate
       |> List.map display_rule)
    state.final_certificate
