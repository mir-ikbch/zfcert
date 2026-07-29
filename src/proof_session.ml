(* ZFCert proof-language evaluation and interactive session state. *)

open Syntax

module StringMap = Map.Make (String)
module StringSet = Syntax.StringSet

(** [Verified] is the application-facing kernel boundary.  This module never
    imports the extracted library directly, and [Verified.state] is abstract. *)
module Verified = Kernel_bridge

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
  display_goals : goal list;
  steps : string list;
}

exception Proof_error of int * string

let trim = String.trim

let split_statements script =
  try Parser.split_statements script with
  | Parser.Statement_error (line, message) ->
      raise (Proof_error (line, message))

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
        raise (Proof_error (line_no,
          "Recursive proposition definition: " ^ name));
      begin match find_definition name definitions with
      | Some definition ->
          let expected = List.length definition.parameters in
          let actual = List.length arguments in
          if expected <> actual then
            raise (Proof_error (line_no,
              Printf.sprintf
                "Definition %s expects %d arguments, but received %d."
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
      | None ->
          raise (Proof_error (line_no,
            "Undefined proposition name: " ^ name))
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
        try parse_formula statement |> unfold line_no definitions
        with Parse_error (_, message) -> raise (Proof_error (line_no, message))
      in
      (names, predicate)

let context_free_vars context =
  List.fold_left (fun acc (_, f) -> StringSet.union acc (free_vars f)) StringSet.empty context

let rec list_index name index = function
  | [] -> None
  | item :: _ when item = name -> Some index
  | _ :: rest -> list_index name (index + 1) rest

let add_free_name environment name =
  if List.mem name environment then environment else environment @ [name]

let canonical_environment goal =
  goal.environment

let db_formula bound environment formula =
  match
    Verified.encode_formula ~bound ~environment formula
  with
  | Ok encoded -> encoded
  | Error message -> raise (Proof_error (1, message))

let source_goal environment (goal : goal) =
  {
    Verified.assumptions =
      List.map (fun (_, formula) -> formula) goal.context;
    Verified.conclusion = goal.target;
    Verified.environment;
  }

let source_goal_canonical goal =
  source_goal (canonical_environment goal) goal

let accept_kernel_result line = function
  | Ok state -> state
  | Error message -> raise (Proof_error (line, message))

let verified_error line =
  raise (Proof_error (line, "Internal kernel-bridge invariant failed."))

let verify_user_transition line command kernel_state rest generated
    before_environment generated_environment =
  let expected =
    List.map (source_goal generated_environment) generated @
    List.map source_goal_canonical rest
  in
  ignore before_environment;
  Verified.checked_step command kernel_state ~expected
  |> accept_kernel_result line

let verify_rule_transition_with_environments line axioms rules kernel_state
    rest generated before_environment =
  let expected =
    List.map
      (fun (goal, environment) -> source_goal environment goal)
      generated
    @ List.map source_goal_canonical rest
  in
  ignore before_environment;
  Verified.checked_rule_run ~axioms rules kernel_state ~expected
  |> accept_kernel_result line

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
  | None -> Error "The conclusion of this fact does not match the current goal."
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
        "This rule requires a formula after :."))
  | Some index ->
      let parameters = trim (String.sub argument 0 index) in
      let formula =
        trim (String.sub argument (index + 1)
          (String.length argument - index - 1))
      in
      if formula = "" then
        raise (Proof_error (line_no, "Expected a formula after :."));
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
  | [] -> raise (Proof_error (line_no, "The proof is already complete."))
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
                    "The current goal is not a registered axiom."))
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
                      "Use: rule axiom separation source x : P."))
                | "replacement", _ ->
                    raise (Proof_error (line_no,
                      "Use: rule axiom replacement source x y : P."))
                | _ ->
                    raise (Proof_error (line_no,
                      "rule axiom accepts only separation or replacement here."))
              in
              if not (alpha_equal instance goal.target) then
                raise (Proof_error (line_no,
                  "The requested schema instance does not match the current goal."));
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
              raise (Proof_error (line_no,
                "Hypothesis not found: " ^ name))
          | Some index ->
              let environment = canonical_environment goal in
              finish (Verified.RHypothesis index) []
                environment environment ("hypothesis " ^ name)
          end
      | "falsum_elim" ->
          if trim rule_argument <> "" then
            raise (Proof_error (line_no,
              "rule falsum_elim takes no arguments."));
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
                  "Use rule impl_intro H with a hypothesis name."));
              if List.mem_assoc name goal.context then
                raise (Proof_error (line_no,
                  "A hypothesis with this name already exists."));
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
                "rule impl_intro requires an implication goal."))
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
                "rule conj_intro requires a conjunction goal."))
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
                "rule disj_intro_l requires a disjunction goal."))
          end
      | "disj_intro_r" ->
          begin match goal.target with
          | Or (_, right) ->
              let environment = canonical_environment goal in
              finish Verified.RDisjIntroR [{ goal with target = right }]
                environment environment "disj_intro_r"
          | _ ->
              raise (Proof_error (line_no,
                "rule disj_intro_r requires a disjunction goal."))
          end
      | "disj_elim" ->
          let names, formulas = split_rule_formula line_no rule_argument in
          let left_name, right_name =
            match names with
            | [left_name; right_name] -> (left_name, right_name)
            | _ ->
                raise (Proof_error (line_no,
                  "Use: rule disj_elim HL HR : P ; Q."))
          in
          let separator =
            match String.index_opt formulas ';' with
            | Some index -> index
            | None ->
                raise (Proof_error (line_no,
                  "Separate the two formulas with ;."))
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
              "Branch hypotheses must use fresh names."));
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
                  "The introduced variable occurs free in a hypothesis."));
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
                "rule all_intro requires a universally quantified goal."))
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
                  "Use: rule all_elim term x : P."))
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
                  "Use rule ex_intro term to provide a witness."));
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
                "rule ex_intro requires an existential goal."))
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
                  "Use: rule ex_elim x H : P."))
          in
          let forbidden =
            StringSet.union (context_free_vars goal.context)
              (free_vars goal.target)
          in
          if StringSet.mem witness forbidden then
            raise (Proof_error (line_no,
              "Existential elimination requires a fresh witness variable."));
          if List.mem_assoc hypothesis goal.context then
            raise (Proof_error (line_no,
              "Existential elimination requires a fresh hypothesis name."));
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
                "rule equal_refl requires a goal of the form t = t."))
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
                  "Use: rule equal_elim s t x : P."))
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
                  "Use: rule cut H : P."))
          in
          if List.mem_assoc hypothesis goal.context then
            raise (Proof_error (line_no,
              "Cut requires a fresh hypothesis name."));
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
          raise (Proof_error (line_no, "Expected a rule name."))
      | unknown ->
          raise (Proof_error (line_no,
            "Unknown inference rule: " ^ unknown))
      end

let execute_tactic line_no state line =
  match state.display_goals with
  | [] -> raise (Proof_error (line_no, "The proof is already complete."))
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
                raise (Proof_error (line_no,
                  "A fact with this name already exists."));
              if source = element then
                raise (Proof_error (line_no,
                  "The source set and element variable must have different names."));
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
                "Use: separation S source x : P."))
          end
      | "replacement" ->
          let names, predicate =
            split_schema_argument line_no state.definitions argument
          in
          begin match names with
          | [fact_name; source; input; output] ->
              if List.mem_assoc fact_name goal.context then
                raise (Proof_error (line_no,
                  "A fact with this name already exists."));
              if source = input || input = output || source = output then
                raise (Proof_error (line_no,
                  "The source, input, and output variables must have distinct names."));
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
                "Use: replacement R source x y : P."))
          end
      | "intro" ->
          begin match goal.target with
          | Imp (premise, target) ->
              if argument = "" then
                raise (Proof_error (line_no, "Expected a hypothesis name."));
              if List.mem_assoc argument goal.context then
                raise (Proof_error (line_no,
                  "A hypothesis with this name already exists."));
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
                raise (Proof_error (line_no,
                  "The introduced variable occurs free in a hypothesis."));
              let next = { goal with target = subst x chosen body } in
              let before_environment = canonical_environment goal in
              let generated_environment = chosen :: before_environment in
              apply_user_transition line_no state Verified.TacIntro
                ("intro " ^ chosen) [next] rest
                before_environment generated_environment
          | Not premise ->
              if argument = "" then
                raise (Proof_error (line_no, "Expected a hypothesis name."));
              if List.mem_assoc argument goal.context then
                raise (Proof_error (line_no,
                  "A hypothesis with this name already exists."));
              let next = {
                context = (argument, premise) :: goal.context;
                target = Bottom;
                environment = goal.environment;
              } in
              let environment = canonical_environment goal in
              apply_user_transition line_no state Verified.TacIntro
                ("intro " ^ argument) [next] rest
                environment environment
          | _ ->
              raise (Proof_error (line_no,
                "intro requires an implication, negation, or universal goal."))
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
              raise (Proof_error (line_no,
                "No hypothesis matches the current goal."))
          end
      | "exact" ->
          begin match lookup_fact argument goal.context with
          | None ->
              raise (Proof_error (line_no,
                "Fact not found: " ^ argument))
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
          | Some _ ->
              raise (Proof_error (line_no,
                "The type of " ^ argument ^ " does not match the current goal."))
          end
      | "apply" ->
          begin match lookup_fact argument goal.context with
          | None ->
              raise (Proof_error (line_no,
                "Theorem, hypothesis, or axiom not found: " ^ argument))
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
              let instantiated =
                List.fold_left
                  (fun current term ->
                     match current with
                     | Forall (bound, body) -> subst bound term body
                     | _ ->
                         raise (Proof_error (line_no,
                           "Too many terms were supplied for universal specialization.")))
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
                      "Too many terms were supplied for universal specialization."))
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
              | Some (And (a, b)) ->
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
                    | _ ->
                        raise (Proof_error (line_no,
                          "Use cases H H1 H2 for conjunctions and equivalences."))
                  in
                  if List.mem_assoc forward_name goal.context || List.mem_assoc backward_name goal.context then
                    raise (Proof_error (line_no,
                      "Case hypotheses must use fresh names."));
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
                  raise (Proof_error (line_no,
                    "cases requires a conjunction, equivalence, or existential hypothesis."))
              end
          | [] ->
              raise (Proof_error (line_no,
                "Expected the name of a hypothesis to eliminate."))
          end
      | "refl" ->
          begin match goal.target with
          | Eq (a, b) when a = b ->
              let environment = canonical_environment goal in
              apply_user_transition line_no state Verified.TacRefl
                "refl" [] rest environment environment
          | _ ->
              raise (Proof_error (line_no,
                "refl requires a goal of the form t = t."))
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
          | _ ->
              raise (Proof_error (line_no,
                "split requires a conjunction or equivalence goal."))
          end
      | "left" ->
          begin match goal.target with
          | Or (a, _) ->
              let next = { goal with target = a } in
              let environment = canonical_environment goal in
              apply_user_transition line_no state Verified.TacLeft
                "left" [next] rest environment environment
          | _ ->
              raise (Proof_error (line_no,
                "left requires a disjunction goal."))
          end
      | "right" ->
          begin match goal.target with
          | Or (_, b) ->
              let next = { goal with target = b } in
              let environment = canonical_environment goal in
              apply_user_transition line_no state Verified.TacRight
                "right" [next] rest environment environment
          | _ ->
              raise (Proof_error (line_no,
                "right requires a disjunction goal."))
          end
      | "use" ->
          if argument = "" then
            raise (Proof_error (line_no,
              "Expected a variable to use as the existential witness."));
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
          | _ ->
              raise (Proof_error (line_no,
                "use requires an existential goal."))
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
          else
            raise (Proof_error (line_no,
              "No contradictory hypotheses were found."))
      | _ ->
          raise (Proof_error (line_no, "Unknown tactic: " ^ command))
      end

let find_colon s =
  match String.index_opt s ':' with
  | Some i -> i
  | None -> raise (Parse_error (0, "A theorem declaration requires :."))

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
          "Use: Definition name parameters... := formula."))
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
    | [] -> raise (Proof_error (line_no, "Expected a definition name."))
  in
  if not (valid_definition_name name) then
    raise (Proof_error (line_no, "Invalid definition name: " ^ name));
  if Option.is_some (find_definition name definitions) then
    raise (Proof_error (line_no,
      "Proposition already defined: " ^ name));
  List.iter
    (fun parameter ->
       if not (valid_definition_name parameter) then
         raise (Proof_error (line_no,
           "Invalid definition parameter: " ^ parameter)))
    parameters;
  let parameter_set = StringSet.of_list parameters in
  if StringSet.cardinal parameter_set <> List.length parameters then
    raise (Proof_error (line_no, "Definition parameters must be unique."));
  let statement =
    String.sub content (assignment + 2)
      (String.length content - assignment - 2)
    |> drop_optional_final_dot
  in
  if statement = "" then
    raise (Proof_error (line_no, "Expected a formula after :=."));
  let body =
    try parse_formula statement |> unfold line_no definitions
    with Parse_error (_, message) -> raise (Proof_error (line_no, message))
  in
  let undeclared = StringSet.diff (free_vars body) parameter_set in
  if not (StringSet.is_empty undeclared) then begin
    let variables = String.concat ", " (StringSet.elements undeclared) in
    raise (Proof_error (line_no,
      "Undeclared free variables in definition body: " ^ variables))
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
  | [] -> raise (Proof_error (1, "The proof script is empty."))
  | (header_line, header) :: tactics ->
      let lower_header = String.lowercase_ascii header in
      let prefix = "theorem " in
      if not (starts_with_at lower_header 0 prefix) then
        raise (Proof_error (header_line,
          "After definitions, use: theorem name : formula."));
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
              raise (Proof_error (line_no,
                "qed cannot close a proof with unresolved goals."));
            if rest <> [] then
              raise (Proof_error (fst (List.hd rest),
                "Unexpected input after qed."));
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
    raise (Proof_error (line, "The proof has unresolved goals."))

let theorem_name state = state.theorem_name
let theorem state = state.theorem
let definitions state = state.definitions

type display_goal = {
  context : (string * formula) list;
  target : formula;
}

let goals state =
  List.map
    (fun (goal : goal) ->
       ({
         context = goal.context;
         target = goal.target;
       } : display_goal))
    state.display_goals
let step_count state = List.length state.steps
let is_complete state = Verified.solved state.kernel_state
