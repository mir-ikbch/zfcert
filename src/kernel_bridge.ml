(** Explicit boundary between the named OCaml frontend and Coq extraction. *)

module Extracted = Zfcert_kernel

type formula = Extracted.formula =
  | Falsum
  | Equal of int * int
  | Member of int * int
  | Conj of formula * formula
  | Disj of formula * formula
  | Impl of formula * formula
  | All of formula
  | Ex of formula

type rule = Extracted.rule =
  | RAxiom
  | RHypothesis of int
  | RFalsumElim
  | RImplIntro
  | RImplElim of formula
  | RConjIntro
  | RConjElimL of formula
  | RConjElimR of formula
  | RDisjIntroL
  | RDisjIntroR
  | RDisjElim of formula * formula
  | RAllIntro
  | RAllElim of formula * int
  | RExIntro of int
  | RExElim of formula
  | REqualRefl
  | REqualElim of formula * int * int
  | RCut of formula

type tactic = Extracted.tactic =
  | TacRule of rule
  | TacIntro
  | TacExact of int
  | TacApply of int
  | TacSpecialize of int * int
  | TacSplit
  | TacLeft
  | TacRight
  | TacUse of int
  | TacRefl
  | TacContradiction
  | TacCases of int

type fixed_axiom = Extracted.fixed_axiom =
  | EmptySet
  | Extensionality
  | Pairing
  | Union
  | PowerSet
  | Foundation
  | Infinity
  | Choice

type state = Extracted.state
type axiom = Extracted.axiom

type goal_view = Extracted.goal_view = {
  assumptions : formula list;
  conclusion : formula;
}

type source_goal = {
  assumptions : Syntax.formula list;
  conclusion : Syntax.formula;
  environment : string list;
}

exception Encoding_error of string

let rec index_of name index = function
  | [] -> None
  | candidate :: _ when candidate = name -> Some index
  | _ :: rest -> index_of name (index + 1) rest

let variable_index bound environment name =
  match index_of name 0 bound with
  | Some index -> index
  | None ->
      begin
        match index_of name 0 environment with
        | Some index -> List.length bound + index
        | None ->
            raise
              (Encoding_error
                 ("Free variable " ^ name
                  ^ " is absent from the kernel environment."))
      end

let rec encode_exn bound environment = function
  | Syntax.Bottom -> Falsum
  | Syntax.Named (name, _) ->
      raise
        (Encoding_error
           ("Unexpanded proposition definition reached the kernel: " ^ name))
  | Syntax.Eq (left, right) ->
      Equal
        (variable_index bound environment left,
         variable_index bound environment right)
  | Syntax.Mem (left, right) ->
      Member
        (variable_index bound environment left,
         variable_index bound environment right)
  | Syntax.Not formula ->
      Impl (encode_exn bound environment formula, Falsum)
  | Syntax.And (left, right) ->
      Conj
        (encode_exn bound environment left,
         encode_exn bound environment right)
  | Syntax.Or (left, right) ->
      Disj
        (encode_exn bound environment left,
         encode_exn bound environment right)
  | Syntax.Imp (left, right) ->
      Impl
        (encode_exn bound environment left,
         encode_exn bound environment right)
  | Syntax.Iff (left, right) ->
      let left = encode_exn bound environment left in
      let right = encode_exn bound environment right in
      Conj (Impl (left, right), Impl (right, left))
  | Syntax.Forall (name, body) ->
      All (encode_exn (name :: bound) environment body)
  | Syntax.Exists (name, body) ->
      Ex (encode_exn (name :: bound) environment body)

let encode_formula ~bound ~environment formula =
  try Ok (encode_exn bound environment formula) with
  | Encoding_error message -> Error message

let start = Extracted.start
let solved = Extracted.solved

let kernel_error = function
  | Extracted.NoGoals -> "the proof state has no goals"
  | Extracted.HypothesisNotFound -> "a hypothesis was not found"
  | Extracted.FormulaMismatch -> "a formula did not match"
  | Extracted.WrongGoalShape -> "the goal has the wrong logical form"

let encode_source_goal goal =
  {
    assumptions =
      List.map
        (encode_exn [] goal.environment)
        goal.assumptions;
    conclusion =
      encode_exn [] goal.environment goal.conclusion;
  }

let check_goal_view next expected =
  try
    let expected = List.map encode_source_goal expected in
    if Extracted.goals next = expected then Ok next
    else
      Error
        "The frontend goal view disagrees with the extracted kernel state."
  with Encoding_error message -> Error message

let checked_step tactic state ~expected =
  match Extracted.step tactic state with
  | Error error ->
      Error ("The extracted kernel rejected the tactic: " ^ kernel_error error)
  | Ok next -> check_goal_view next expected

let checked_rule_run ~axioms rules state ~expected =
  match Extracted.rule_run ~axioms rules state with
  | Error error ->
      Error ("The extracted kernel rejected the rule: " ^ kernel_error error)
  | Ok next -> check_goal_view next expected

let fixed_axiom = Extracted.fixed_axiom
let separation_axiom = Extracted.separation_axiom
let replacement_axiom = Extracted.replacement_axiom
let instantiate = Extracted.instantiate
let separation_instance = Extracted.separation_instance
let replacement_instance = Extracted.replacement_instance
