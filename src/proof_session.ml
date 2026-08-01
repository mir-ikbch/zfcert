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
  context : (string * formula) list;
  target : formula;
}

type proposition_alias = {
  alias_name : string;
  parameters : string list;
  body : formula;
}

(** A [Choose] declaration extends the extracted global environment.  The
    source existential is proved and finalized before the extracted kernel
    accepts the new constant and its named fact. *)
type choice_declaration = {
  choice_line : int;
  choice_witness : string;
  choice_hypothesis : string;
  choice_source : string;
  choice_terms : string list;
}

type skolem_declaration = {
  skolem_line : int;
  skolem_function : string;
  skolem_hypothesis : string;
  skolem_source : string;
}

type global_declaration =
  | ChoiceDeclaration of choice_declaration
  | SkolemDeclaration of skolem_declaration

type session = {
  theorem_name : string;
  theorem : formula;
  aliases : proposition_alias list;
  global_environment : Extracted.environment;
  kernel_state : Extracted.state;
  final_certificate : Extracted.certificate option;
  steps : string list;
}

exception Proof_error of int * string

let trim = String.trim

let split_statements script =
  try Parser.split_statements script with
  | Parser.Statement_error (line, message) ->
      raise (Proof_error (line, message))

let find_alias name aliases =
  List.find_opt
    (fun alias -> alias.alias_name = name)
    aliases

let substitution_variables substitutions =
  StringMap.fold
    (fun variable term variables ->
       StringSet.add variable (StringSet.add term variables))
    substitutions
    StringSet.empty

let substitute_surface_term substitutions term =
  let rec go = function
    | Name name ->
        Name (Option.value (StringMap.find_opt name substitutions) ~default:name)
    | App (name, arguments) -> App (name, List.map go arguments)
  in
  go term

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
      Eq (substitute_surface_term substitutions a,
          substitute_surface_term substitutions b)
  | Mem (a, b) ->
      Mem (substitute_surface_term substitutions a,
           substitute_surface_term substitutions b)
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

let rec unfold_formula line_no aliases visiting = function
  | Named (name, arguments) ->
      if StringSet.mem name visiting then
        raise (Proof_error (line_no,
          "Recursive proposition alias: " ^ name));
      begin match find_alias name aliases with
      | Some alias ->
          let expected = List.length alias.parameters in
          let actual = List.length arguments in
          if expected <> actual then
            raise (Proof_error (line_no,
              Printf.sprintf
                "Alias %s expects %d arguments, but received %d."
                name expected actual));
          let substitutions =
            List.fold_left2
              (fun substitutions parameter argument ->
                 StringMap.add parameter argument substitutions)
              StringMap.empty alias.parameters arguments
          in
          let instantiated = subst_many substitutions alias.body in
          unfold_formula line_no aliases
            (StringSet.add name visiting) instantiated
      | None ->
          raise (Proof_error (line_no,
            "Undefined proposition name: " ^ name))
      end
  | Bottom -> Bottom
  | Eq (a, b) -> Eq (a, b)
  | Mem (a, b) -> Mem (a, b)
  | Not f -> Not (unfold_formula line_no aliases visiting f)
  | And (a, b) ->
      And (unfold_formula line_no aliases visiting a,
           unfold_formula line_no aliases visiting b)
  | Or (a, b) ->
      Or (unfold_formula line_no aliases visiting a,
          unfold_formula line_no aliases visiting b)
  | Imp (a, b) ->
      Imp (unfold_formula line_no aliases visiting a,
           unfold_formula line_no aliases visiting b)
  | Iff (a, b) ->
      Iff (unfold_formula line_no aliases visiting a,
           unfold_formula line_no aliases visiting b)
  | Forall (x, f) ->
      Forall (x, unfold_formula line_no aliases visiting f)
  | Exists (x, f) ->
      Exists (x, unfold_formula line_no aliases visiting f)

let unfold line_no aliases formula =
  unfold_formula line_no aliases StringSet.empty formula

let split_first_word line =
  match String.index_opt line ' ' with
  | None -> (line, "")
  | Some i -> (String.sub line 0 i, trim (String.sub line (i + 1) (String.length line - i - 1)))

let split_schema_argument line_no aliases argument =
  match String.index_opt argument ':' with
  | None ->
      raise (Proof_error (line_no,
        "A schema instance requires : followed by a formula."))
  | Some i ->
      let names =
        String.sub argument 0 i
        |> trim
        |> String.split_on_char ' '
        |> List.map trim
        |> List.filter (fun name -> name <> "")
      in
      let statement = trim (String.sub argument (i + 1) (String.length argument - i - 1)) in
      if statement = "" then
        raise (Proof_error (line_no, "Expected a formula after :."));
      let predicate =
        try parse_formula statement |> unfold line_no aliases
        with Parse_error (_, message) -> raise (Proof_error (line_no, message))
      in
      (names, predicate)

let context_free_vars context =
  List.fold_left (fun acc (_, f) -> StringSet.union acc (free_vars f)) StringSet.empty context

let kernel_formula formula =
  Kernel_syntax.to_kernel formula

let materialize_goals line state =
  match Extracted.goals state.kernel_state with
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
             List.map
               (fun (name, formula) ->
                  (name, Kernel_syntax.of_kernel formula))
               kernel_goal.assumptions
           in
           let target =
             Kernel_syntax.of_kernel kernel_goal.conclusion
           in
           {
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
  | None -> Error "The conclusion of this fact does not match the current goal."
  | Some sub ->
      let premises = List.map (instantiate_formula sub) premises in
      Ok (premises, sub)

let add_step state text kernel_state =
  { state with
    kernel_state;
    final_certificate = None;
    steps = state.steps @ [text];
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

let parse_formula_at line_no aliases text =
  try parse_formula (trim text) |> unfold line_no aliases
  with Parse_error (_, message) -> raise (Proof_error (line_no, message))

let parse_surface_term line_no text =
  try
    match parse_formula (trim text ^ " = " ^ trim text) with
    | Eq (term, _) -> term
    | _ -> raise (Proof_error (line_no, "Expected a term."))
  with Parse_error (_, message) -> raise (Proof_error (line_no, message))

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
  let parse_formula text =
    parse_formula_at line_no state.aliases text
  in
  let request =
    try Rule_parser.parse ~parse_formula argument with
    | Rule_parser.Error message ->
        raise (Proof_error (line_no, message))
  in
  let kernel_state =
    Extracted.execute_rule request state.kernel_state
    |> accept_kernel_result line_no "rule"
  in
  add_step state (Rule_parser.description argument) kernel_state

let specialize_rules line_no fact terms =
  let rec build current remaining rules =
    match remaining, current with
    | [], _ -> (current, rules)
    | term :: rest, Forall (binder, body) ->
        let surface_term = parse_surface_term line_no term in
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

let close_fact line_no name context =
  if List.mem_assoc name context then
    (Extracted.NRHypothesis name, [])
  else
    match fixed_axiom_kind (String.lowercase_ascii name) with
    | Some kind ->
        (Extracted.NRAxiom, [Extracted.fixed_axiom kind])
    | None -> verified_error line_no

let words text =
  text
  |> String.split_on_char ' '
  |> List.map trim
  |> List.filter (fun word -> word <> "")

let parse_choice_words line_no command argument =
  match words argument with
  | witness :: hypothesis :: from_word :: source :: terms
    when String.lowercase_ascii from_word = "from" ->
      (witness, hypothesis, source, terms)
  | _ ->
      raise (Proof_error (line_no,
        Printf.sprintf
          "Use: %s witness hypothesis from fact term1 term2."
          command))

let parse_skolem_words line_no argument =
  match words argument with
  | function_name :: hypothesis :: from_word :: source :: []
    when String.lowercase_ascii from_word = "from" ->
      (function_name, hypothesis, source)
  | _ ->
      raise (Proof_error (line_no,
        "Use: Skolem function hypothesis from fact."))

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
        match lookup_fact source goal.context with
        | Some fact -> fact
        | None ->
            raise (Proof_error (line_no,
              "Existential fact not found: " ^ source))
      in
      let instantiated, all_rules =
        specialize_rules line_no fact terms
      in
      begin match instantiated with
      | Exists _ ->
          let close_rule, axioms =
            close_fact line_no source goal.context
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

(** Prove the existential selected by a [Choose] declaration, replay its
    certificate, and ask the extracted global environment to add the fresh
    constant and fact.  OCaml plans the certificate but never constructs or
    mutates the logical environment itself. *)
let declare_global_choice environment choice =
  let line_no = choice.choice_line in
  let context =
    Extracted.environment_facts environment
    |> List.map (fun (name, formula) ->
         (name, Kernel_syntax.of_kernel formula))
  in
  let fact =
    match lookup_fact choice.choice_source context with
    | Some fact -> fact
    | None ->
        raise (Proof_error (line_no,
          "Existential fact not found: " ^ choice.choice_source))
  in
  let instantiated, all_rules =
    specialize_rules line_no fact choice.choice_terms
  in
  match instantiated with
  | Exists _ ->
      let close_rule, axioms =
        close_fact line_no choice.choice_source context
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
        ~constant:choice.choice_witness
        ~fact:choice.choice_hypothesis
        ~source:(kernel_formula instantiated)
        ~proof:certificate
        environment
      |> accept_kernel_result line_no "global choice declaration"
  | _ ->
      raise (Proof_error (line_no,
        "The selected fact does not become existential after specialization."))

let declare_global_skolem environment declaration =
  let line_no = declaration.skolem_line in
  let context =
    Extracted.environment_facts environment
    |> List.map (fun (name, formula) ->
         (name, Kernel_syntax.of_kernel formula))
  in
  let source =
    match lookup_fact declaration.skolem_source context with
    | Some fact -> fact
    | None ->
        raise (Proof_error (line_no,
          "Universal-existential fact not found: " ^ declaration.skolem_source))
  in
  let close_rule, axioms = close_fact line_no declaration.skolem_source context in
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
    ~function_name:declaration.skolem_function
    ~fact:declaration.skolem_hypothesis
    ~source:(kernel_formula source)
    ~proof:certificate
    environment
  |> accept_kernel_result line_no "global Skolem declaration"

let execute_tactic line_no state line =
  match materialize_goals line_no state with
  | [] -> raise (Proof_error (line_no, "The proof is already complete."))
  | goal :: _ ->
      let command, argument = split_first_word line in
      let command = String.lowercase_ascii command in
      begin match command with
      | "rule" -> execute_rule line_no state argument
      | "obtain" -> execute_obtain line_no state "obtain" argument
      | "separation" ->
          let names, predicate =
            split_schema_argument line_no state.aliases argument
          in
          begin match names with
          | [fact_name; source; element] ->
              if source = element then
                raise (Proof_error (line_no,
                  "The source set and element variable must have different names."));
              let kernel_state =
                Extracted.separation_tactic_step
                  ~fact:fact_name ~source ~element
                  (kernel_formula predicate) state.kernel_state
                |> accept_kernel_result line_no "separation tactic"
              in
              add_step state ("separation " ^ fact_name) kernel_state
          | _ ->
              raise (Proof_error (line_no,
                "Use: separation S source x : P."))
          end
      | "replacement" ->
          let names, predicate =
            split_schema_argument line_no state.aliases argument
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
      | "intro" ->
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
          begin match lookup_fact argument goal.context with
          | None ->
              raise (Proof_error (line_no,
                "Fact not found: " ^ argument))
          | Some fact when alpha_equal fact goal.target ->
              let axioms, rule =
                if List.mem_assoc argument goal.context then
                  ([], Extracted.NRHypothesis argument)
                else
                  let axiom =
                    match fixed_axiom_kind
                      (String.lowercase_ascii argument) with
                    | Some kind -> Extracted.fixed_axiom kind
                    | None -> verified_error line_no
                  in
                  ([axiom], Extracted.NRAxiom)
              in
              apply_certificate_program line_no state
                [checked_step ~axioms rule]
                ("exact " ^ argument)
          | Some _ ->
              raise (Proof_error (line_no,
                "The type of " ^ argument ^ " does not match the current goal."))
          end
      | "apply" ->
          let apply_words = words argument in
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
                match List.assoc_opt source_name goal.context with
                | Some formula -> formula
                | None ->
                    raise (Proof_error (line_no,
                      "Hypothesis not found: " ^ source_name))
              in
              begin match lookup_fact fact_name goal.context with
              | None ->
                  raise (Proof_error (line_no,
                    "Theorem, hypothesis, or axiom not found: " ^ fact_name))
              | Some fact ->
                  let metas, body = decompose_forall fact in
                  let premises, conclusion = decompose_imp body in
                  begin match premises with
                  | [premise] ->
                      begin match match_formula metas premise source_formula with
                      | None ->
                          raise (Proof_error (line_no,
                            "The selected hypothesis does not match the premise of "
                            ^ fact_name ^ "."))
                      | Some substitutions ->
                          let instantiated_premise =
                            instantiate_formula substitutions premise
                          in
                          let instantiated_conclusion =
                            instantiate_formula substitutions conclusion
                          in
                          let rec forall_names names = function
                            | Forall (name, body) ->
                                forall_names (name :: names) body
                            | body -> (List.rev names, body)
                          in
                          let binders, _ = forall_names [] fact in
                          let terms =
                            List.map
                              (fun binder ->
                                 Option.value
                                   (StringMap.find_opt binder substitutions)
                                   ~default:binder)
                              binders
                          in
                          let _, all_commands =
                            specialize_rules line_no fact terms
                          in
                          let close_command, axioms =
                            close_fact line_no fact_name goal.context
                          in
                          let program =
                            [checked_step
                               (Extracted.NRCut
                                  (new_name,
                                   kernel_formula instantiated_conclusion));
                             checked_step
                               (Extracted.NRImplElim
                                  (kernel_formula instantiated_premise))]
                            @ List.map checked_step all_commands
                            @ [checked_step ~axioms close_command;
                               checked_step
                                 (Extracted.NRHypothesis source_name)]
                          in
                          apply_certificate_program line_no state program
                            ("apply " ^ fact_name ^ " in " ^ source_name
                             ^ " as " ^ new_name)
                      end
                  | _ ->
                      raise (Proof_error (line_no,
                        "apply ... in ... as currently requires a fact with "
                        ^ "exactly one implication premise."))
                  end
              end
          | [fact_name] ->
              begin match lookup_fact fact_name goal.context with
              | None ->
                  raise (Proof_error (line_no,
                    "Theorem, hypothesis, or axiom not found: " ^ fact_name))
              | Some fact ->
                  begin match apply_fact fact goal with
                  | Error message -> raise (Proof_error (line_no, message))
                  | Ok (premises, substitutions) ->
                      let rec forall_names names = function
                        | Forall (name, body) ->
                            forall_names (name :: names) body
                        | body -> (List.rev names, body)
                      in
                      let binders, _ = forall_names [] fact in
                      let terms =
                        List.map
                          (fun binder ->
                             Option.value
                               (StringMap.find_opt binder substitutions)
                               ~default:binder)
                          binders
                      in
                      let _, all_commands =
                        specialize_rules line_no fact terms
                      in
                      let implication_commands =
                        List.rev premises
                        |> List.map (fun premise ->
                             Extracted.NRImplElim (kernel_formula premise))
                      in
                      let close_command, axioms =
                        close_fact line_no fact_name goal.context
                      in
                      let program =
                        List.map checked_step
                          (implication_commands @ all_commands)
                        @ [checked_step ~axioms close_command]
                      in
                      apply_certificate_program line_no state program
                        ("apply " ^ fact_name)
                  end
              end
          | _ ->
              raise (Proof_error (line_no,
                "Use apply H or apply H0 in H as H1."))
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
                match lookup_fact source goal.context with
                | Some fact -> fact
                | None ->
                    raise (Proof_error (line_no,
                      "Universally quantified fact not found: " ^ source))
              in
              let instantiated, all_commands =
                specialize_rules line_no fact terms
              in
              let close_command, axioms =
                close_fact line_no source goal.context
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
          let words =
            String.split_on_char ' ' argument
            |> List.map trim
            |> List.filter (fun word -> word <> "")
          in
          begin match words with
          | fact_name :: names ->
              begin match List.assoc_opt fact_name goal.context with
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
              let witness = parse_surface_term line_no argument in
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

let parse_alias line_no aliases line =
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
    |> String.split_on_char ' '
    |> List.map trim
    |> List.filter (fun word -> word <> "")
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
  List.iter
    (fun parameter ->
       if not (valid_alias_name parameter) then
         raise (Proof_error (line_no,
           "Invalid alias parameter: " ^ parameter)))
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
    try parse_formula statement |> unfold line_no aliases
    with Parse_error (_, message) -> raise (Proof_error (line_no, message))
  in
  let undeclared = StringSet.diff (free_vars body) parameter_set in
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

let analyze_script script =
  let meaningful = split_statements script in
  let rec read_declarations aliases declarations = function
    | (line_no, line) :: rest
      when starts_with_at (String.lowercase_ascii line) 0 "alias " ->
        read_declarations
          (parse_alias line_no aliases line) declarations rest
    | (line_no, line) :: rest
      when starts_with_at (String.lowercase_ascii line) 0 "choose " ->
        let prefix = "choose " in
        let argument =
          trim (String.sub line (String.length prefix)
            (String.length line - String.length prefix))
        in
        let witness, hypothesis, source, terms =
          parse_choice_words line_no "Choose" argument
        in
        let choice = {
          choice_line = line_no;
          choice_witness = witness;
          choice_hypothesis = hypothesis;
          choice_source = source;
          choice_terms = terms;
        } in
        read_declarations aliases
          (declarations @ [ChoiceDeclaration choice]) rest
    | (line_no, line) :: rest
      when starts_with_at (String.lowercase_ascii line) 0 "skolem " ->
        let prefix = "skolem " in
        let argument =
          trim (String.sub line (String.length prefix)
            (String.length line - String.length prefix))
        in
        let function_name, hypothesis, source =
          parse_skolem_words line_no argument
        in
        let declaration = {
          skolem_line = line_no;
          skolem_function = function_name;
          skolem_hypothesis = hypothesis;
          skolem_source = source;
        } in
        read_declarations aliases
          (declarations @ [SkolemDeclaration declaration]) rest
    | rest -> (aliases, declarations, rest)
  in
  let apply_declarations environment steps declarations =
    List.fold_left
      (fun (environment, steps) declaration ->
         match declaration with
         | ChoiceDeclaration choice ->
             let environment = declare_global_choice environment choice in
             let description =
               String.concat " "
                 ("Choose" :: choice.choice_witness ::
                  choice.choice_hypothesis :: "from" ::
                  choice.choice_source :: choice.choice_terms)
             in
             (environment, steps @ [description])
         | SkolemDeclaration declaration ->
             let environment = declare_global_skolem environment declaration in
             let description =
               String.concat " "
                 ["Skolem"; declaration.skolem_function;
                  declaration.skolem_hypothesis; "from";
                  declaration.skolem_source]
             in
             (environment, steps @ [description]))
      (environment, steps) declarations
  in
  let rec process aliases environment steps statements =
    let aliases, declarations, proof =
      read_declarations aliases [] statements
    in
    let global_environment, declaration_steps =
      apply_declarations environment steps declarations
    in
    match proof with
    | [] when aliases <> [] || declarations <> [] ->
        let kernel_state =
          Extracted.start_in_environment global_environment Extracted.NFalsum
          |> accept_kernel_result 1 "initial goal"
        in
        let declarations = {
          theorem_name = "";
          theorem = Bottom;
          aliases;
          global_environment;
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
            "After aliases, choices, and Skolem declarations, use: theorem name : formula."));
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
          try parse_formula statement |> unfold header_line aliases
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
          global_environment;
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
              let certificate =
                Extracted.finalize state.kernel_state
                |> accept_kernel_result line_no "final certificate replay"
              in
              let state = { state with final_certificate = Some certificate } in
              if rest = [] then (state, true)
              else
                let next_environment =
                  Extracted.declare_fact
                    ~fact:state.theorem_name
                    ~source:(kernel_formula state.theorem)
                    ~proof:certificate
                    state.global_environment
                  |> accept_kernel_result line_no "global theorem declaration"
                in
                process aliases next_environment state.steps rest
          | (line_no, line) :: rest ->
              run (execute_tactic line_no state line) rest
        in
        run initial tactics
  in
  process [] Extracted.empty_environment [] meaningful

let check_script script =
  let state, _ = analyze_script script in
  if state.theorem_name = "" then state
  else if Extracted.solved state.kernel_state then
    begin match state.final_certificate with
    | Some _ -> state
    | None ->
        let line = List.length (String.split_on_char '\n' script) in
        let certificate =
          Extracted.finalize state.kernel_state
          |> accept_kernel_result line "final certificate replay"
        in
        { state with final_certificate = Some certificate }
    end
  else
    let line = List.length (String.split_on_char '\n' script) in
    raise (Proof_error (line, "The proof has unresolved goals."))

let theorem_name state = state.theorem_name
let theorem state = state.theorem
let aliases state = state.aliases
let global_constants state =
  Extracted.environment_constants state.global_environment
let global_facts state =
  Extracted.environment_facts state.global_environment
  |> List.map (fun (name, formula) ->
       (name, Kernel_syntax.of_kernel formula))

type display_goal = {
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
        left right (display_kernel_formula predicate)
  | Extracted.NRCut (hypothesis, lemma) ->
      Printf.sprintf "cut %s : %s"
        hypothesis (display_kernel_formula lemma)

let certificate_rules state =
  Option.map
    (fun certificate ->
       Extracted.certificate_rules certificate
       |> List.map display_rule)
    state.final_certificate
